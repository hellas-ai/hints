//! SNARK for certifying weighted aggregation (implementation detail)

use ark_ec::VariableBaseMSM;
use ark_ec::{pairing::Pairing, CurveGroup};
use ark_ff::PrimeField;
use ark_poly::{univariate::DensePolynomial, Polynomial};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{One, Zero};

use crate::utils::{self};
use crate::{kzg::*, HintsError, PublicKey};

mod hints;
mod prover;
mod verifier;

pub use hints::*;
pub use prover::*;
pub use verifier::*;

// ark_blst includes a GPU-"accelerated" backend for msm but it's actually
// substantially slower than the CPU in benchmarks (measured on an M2 Pro)

//pub type Curve = ark_blst::Bls12;

pub type Curve = ark_bls12_381::Bls12_381;

pub type KZG = KZG10<Curve, UniPoly381>;
pub type UniPoly381 = DensePolynomial<<Curve as Pairing>::ScalarField>;
pub type F = <Curve as Pairing>::ScalarField;
pub type G1 = <Curve as Pairing>::G1Affine;
pub type G2 = <Curve as Pairing>::G2Affine;
pub type G1Projective = <Curve as Pairing>::G1;
pub type G2Projective = <Curve as Pairing>::G2;

/// Global data for the SNARK
///
/// Contains the KZG10 parameters and the cache of precomputed Lagrange polynomials and commitments.
#[derive(Clone, Debug)]
pub struct GlobalData {
    pub params: UniversalParams<Curve>,
    pub cache: Cache,
}

pub(crate) const LOCKSTITCH_DOMAIN: &str = "hints-bls12-381-snark";

// Trait to abstract the source of Fiat-Shamir data (VerifierKey or AggregationKey)
pub(crate) trait FiatShamirTranscriptData {
    fn mix_fs_data(&self, transcript: &mut lockstitch::Protocol) -> Result<(), HintsError>;
}

#[derive(Clone, Debug, Default, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProofCommitments {
    pub psw_of_x_com: G1,
    pub b_of_x_com: G1,
    pub psw_wff_q_of_x_com: G1,
    pub psw_check_q_of_x_com: G1,
    pub b_wff_q_of_x_com: G1,
    pub b_check_q_of_x_com: G1,
    pub sk_q1_com: G1,
    pub sk_q2_com: G1,
}

impl Cache {
    /// Create a new cache from the given parameters.
    pub fn from_params(max_degree: usize, params: &UniversalParams<Curve>) -> Self {
        let lagrange_polynomials: Vec<_> = (0..max_degree)
            .map(|i| utils::lagrange_poly(max_degree, i))
            .collect();

        let lagrange_coms_g1 = lagrange_polynomials
            .iter()
            .map(|h| KZG10::commit_g1(params, h).unwrap())
            .collect();

        let lagrange_coms_g2 = lagrange_polynomials
            .iter()
            .map(|h| KZG10::commit_g2(params, h).unwrap())
            .collect();

        let lockstitch = lockstitch::Protocol::new(LOCKSTITCH_DOMAIN);

        Cache {
            lagrange_polynomials,
            lagrange_coms_g1,
            lagrange_coms_g2,
            lockstitch,
        }
    }
}

impl GlobalData {
    /// Create a new global data from the given parameters.
    pub fn from_params(max_degree: usize, params: UniversalParams<Curve>) -> Self {
        let cache = Cache::from_params(max_degree, &params);
        Self { params, cache }
    }
}

/// Cache of precomputed Lagrange polynomials and commitments.
#[derive(Clone, Debug)]
pub struct Cache {
    pub lagrange_polynomials: Vec<DensePolynomial<F>>,
    pub lagrange_coms_g1: Vec<G1>,
    pub lagrange_coms_g2: Vec<G2>,
    pub lockstitch: lockstitch::Protocol,
}

fn compute_apk(all_pks: &[PublicKey], all_l_polys: &[DensePolynomial<F>], full_bitmap: &[F]) -> G1 {
    let n = full_bitmap.len();
    assert_eq!(all_pks.len(), n, "compute_apk pks length mismatch");
    assert!(
        all_l_polys.len() >= n,
        "compute_apk l_polys length mismatch"
    );

    let unwrapped_pks: Vec<G1> = all_pks.iter().map(|pk| pk.0).collect();
    let exponents: Vec<F> = (0..n)
        .map(|i| {
            let l_i_of_x = &all_l_polys[i];
            let l_i_of_0 = l_i_of_x.evaluate(&F::zero());
            if full_bitmap[i].is_one() {
                l_i_of_0
            } else {
                F::zero()
            }
        })
        .collect();

    <<Curve as Pairing>::G1 as VariableBaseMSM>::msm(&unwrapped_pks, &exponents)
        .expect("MSM failed in compute_apk")
        .into_affine()
}

fn mix_object<T: CanonicalSerialize>(
    transcript: &mut lockstitch::Protocol,
    label: &str,
    obj: &T,
) -> Result<(), HintsError> {
    let mut buf = Vec::new();
    obj.serialize_uncompressed(&mut buf)?;
    transcript.mix(label, &buf);
    Ok(())
}

// Helper function to derive a field element from the transcript
fn derive_field_element(transcript: &mut lockstitch::Protocol, label: &str) -> F {
    // Derive 64 bytes, which is usually sufficient for field elements (e.g., 381 bits need ~48 bytes)
    // We reduce modulo the field order.
    let mut buf = [0u8; 64];
    transcript.derive(label, &mut buf);
    F::from_le_bytes_mod_order(&buf)
}

// Function to compute the Fiat-Shamir challenge `r`
// Common logic used by both prover and verifier
pub(crate) fn compute_challenge_r(
    base_transcript: &lockstitch::Protocol,
    vp_or_ak: &impl FiatShamirTranscriptData, // Use trait for common data access
    agg_pk: &G1,
    agg_weight: &F,
    commitments: &ProofCommitments,
) -> Result<F, HintsError> {
    let mut transcript = base_transcript.clone(); // Start from the base state

    // Mix common parameters and commitments known by verifier before challenge
    vp_or_ak.mix_fs_data(&mut transcript)?;

    // Mix prover's round 1 messages (commitments)
    mix_object(&mut transcript, "agg_pk", agg_pk)?;
    mix_object(&mut transcript, "agg_weight", agg_weight)?;
    mix_object(&mut transcript, "psw_com", &commitments.psw_of_x_com)?;
    mix_object(&mut transcript, "b_com", &commitments.b_of_x_com)?;
    mix_object(
        &mut transcript,
        "psw_wff_q_com",
        &commitments.psw_wff_q_of_x_com,
    )?;
    mix_object(
        &mut transcript,
        "psw_check_q_com",
        &commitments.psw_check_q_of_x_com,
    )?;
    mix_object(
        &mut transcript,
        "b_wff_q_com",
        &commitments.b_wff_q_of_x_com,
    )?;
    mix_object(
        &mut transcript,
        "b_check_q_com",
        &commitments.b_check_q_of_x_com,
    )?;
    mix_object(&mut transcript, "sk_q1_com", &commitments.sk_q1_com)?;
    mix_object(&mut transcript, "sk_q2_com", &commitments.sk_q2_com)?;

    Ok(derive_field_element(&mut transcript, "challenge_r"))
}

impl FiatShamirTranscriptData for VerifierKey {
    fn mix_fs_data(&self, transcript: &mut lockstitch::Protocol) -> Result<(), HintsError> {
        mix_object(transcript, "domain_max", &self.domain_max)?;
        mix_object(transcript, "ln-1_com", &self.l_n_minus_1_of_x_com)?;
        // Note: We mix the VerifierKey's w_of_x_com, which is the *initial* one before adjustment
        mix_object(transcript, "w_com", &self.w_of_x_com)?;
        mix_object(transcript, "sk_com", &self.sk_of_x_com)?;
        mix_object(transcript, "vanish_com", &self.vanishing_com)?;
        mix_object(transcript, "x_mono_com", &self.x_monomial_com)?;
        Ok(())
    }
}

impl FiatShamirTranscriptData for AggregationKey {
    fn mix_fs_data(&self, transcript: &mut lockstitch::Protocol) -> Result<(), HintsError> {
        // We need to mix the *same* public parameters the verifier uses.
        // These were computed during finish_setup and stored in VerifierKey,
        // and then copied/derived into AggregationKey.
        mix_object(transcript, "domain_max", &self.domain_max)?;
        // g0, h0, h1 are implicitly part of the global params used for commitments
        // Mix the commitments that correspond to the ones in VerifierKey
        mix_object(transcript, "ln-1_com", &self.vk_l_n_minus_1_com)?;
        mix_object(transcript, "w_com", &self.vk_w_of_x_com)?;
        mix_object(transcript, "sk_com", &self.vk_sk_of_x_com)?;
        mix_object(transcript, "vanish_com", &self.vk_vanishing_com)?;
        mix_object(transcript, "x_mono_com", &self.vk_x_monomial_com)?;
        Ok(())
    }
}
