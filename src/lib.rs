#![doc = include_str!("../README.md")]

use ark_crypto_primitives::crh::sha256::Sha256;
use ark_ec::{
    bls12::Bls12Config, hashing::map_to_curve_hasher::MapToCurveBasedHasher, pairing::Pairing,
    AffineRepr, CurveGroup,
};
use ark_ff::{Field, One, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_std::{rand::RngCore, vec::Vec, UniformRand};

use ark_ec::hashing::curve_maps::wb::WBMap;

pub mod kzg;
pub mod snark;
pub(crate) mod trusted_setup;
pub mod utils;

use kzg::UniversalParams;
use snark::*;
pub use trusted_setup::*;

/// Hints Errors
#[derive(Debug)]
pub enum HintsError {
    KzgSetupError(kzg::Error),
    PolynomialDegreeTooLarge,
    ProofVerificationError(String),
    HintVerificationError(String),
    VerificationStep(&'static str),
    TrustedSetupError(trusted_setup::TrustedSetupError),
    InvalidInput(String),
    ThresholdNotMet,
    BlsVerificationFailed,
    SerializationError(SerializationError),
    #[cfg(feature = "parallel")]
    RayonJoinError,
}

impl From<kzg::Error> for HintsError {
    fn from(e: kzg::Error) -> Self {
        HintsError::KzgSetupError(e)
    }
}

impl From<SerializationError> for HintsError {
    fn from(e: SerializationError) -> Self {
        HintsError::SerializationError(e)
    }
}

impl std::fmt::Display for HintsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HintsError::KzgSetupError(e) => write!(f, "KZG Setup Error: {:?}", e),
            HintsError::PolynomialDegreeTooLarge => {
                write!(f, "Polynomial degree too large for CRS")
            }
            HintsError::ProofVerificationError(s) => write!(f, "Proof verification failed: {}", s),
            HintsError::HintVerificationError(s) => write!(f, "Hint verification failed: {}", s),
            HintsError::VerificationStep(s) => write!(f, "failing step: {}", s),
            HintsError::TrustedSetupError(e) => write!(f, "Trusted setup error: {:?}", e),
            HintsError::InvalidInput(s) => write!(f, "Invalid input: {}", s),
            HintsError::ThresholdNotMet => write!(f, "Aggregated weight does not meet threshold"),
            HintsError::BlsVerificationFailed => {
                write!(f, "Aggregated BLS signature verification failed")
            }
            HintsError::SerializationError(e) => write!(f, "Serialization error: {}", e),
            #[cfg(feature = "parallel")]
            HintsError::RayonJoinError => write!(f, "Parallel computation join error"),
        }
    }
}

impl From<trusted_setup::TrustedSetupError> for HintsError {
    fn from(e: trusted_setup::TrustedSetupError) -> Self {
        HintsError::TrustedSetupError(e)
    }
}

impl std::error::Error for HintsError {}

/// BLS Secret Key
#[derive(
    Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, CanonicalSerialize, CanonicalDeserialize,
)]
pub struct SecretKey(pub F);

impl SecretKey {
    pub fn random(rng: &mut impl RngCore) -> Self {
        Self(F::rand(rng))
    }

    pub fn dummy() -> Self {
        Self(F::from(-1i64))
    }

    pub fn public(&self, gd: &GlobalData) -> PublicKey {
        PublicKey((gd.params.powers_of_g[0] * self.0).into_affine())
    }

    pub fn sign(&self, msg: &[u8]) -> PartialSignature {
        sign(self, msg)
    }
}

/// BLS Public Key
#[derive(Copy, Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct PublicKey(pub G1);

/// BLS Partial Signature
#[derive(Copy, Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct PartialSignature(pub G2);

/// Final Aggregated Signature
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Signature {
    /// Aggregated BLS signature σ' = H(m)^aSK
    pub agg_sig_prime: G2,
    /// The threshold for the signature
    pub threshold: F,
    /// The SNARK proof π
    pub proof: Proof,
}

impl Signature {
    pub fn verify(
        &self,
        gd: &GlobalData,
        vp: &VerifierKey,
        msg: &[u8],
    ) -> Result<bool, HintsError> {
        verify_aggregate(gd, vp, self, msg)
    }
}

/// Setup: Generate the Common Reference String (CRS) for a maximum degree.
/// max_degree should be at least the maximum anticipated committee size n.
pub fn setup_insecure<R: RngCore>(
    max_degree: usize,
    rng: &mut R,
) -> Result<GlobalData, HintsError> {
    // The underlying KZG needs degree M, where the polynomials can go up to M.
    // Our polynomials (e.g., Z(x)) have degree n, where n is committee size.
    // So max_degree should be >= n.
    if max_degree == 0 {
        return Err(HintsError::InvalidInput(
            "max_degree must be > 0".to_string(),
        ));
    }
    let params = KZG::setup_insecure(max_degree, rng)?;
    Ok(GlobalData::from_params(max_degree, params))
}

/// Setup: Generate the Common Reference String (CRS) for a maximum degree.
///
/// Uses the Ethereum KZG trusted setup.
pub fn setup_eth(max_degree: usize) -> Result<GlobalData, HintsError> {
    let ts = crate::trusted_setup::JsonTrustedSetup::default().deserialize::<Curve>()?;
    let params = UniversalParams {
        powers_of_g: ts.g1_points.to_vec(),
        powers_of_h: ts.g2_points.to_vec(),
    };
    Ok(GlobalData::from_params(max_degree, params))
}

/// Generate a BLS key pair.
pub fn keygen<R: RngCore>(crs: &GlobalData, rng: &mut R) -> (SecretKey, PublicKey) {
    let sk = F::rand(rng);
    let pk = crs.params.powers_of_g[0]
        .mul_bigint(sk.into_bigint())
        .into_affine();
    (SecretKey(sk), PublicKey(pk))
}

/// Create a BLS partial signature.
pub fn sign(sk: &SecretKey, msg: &[u8]) -> PartialSignature {
    let h_m = utils::hash_to_g2::<
        MapToCurveBasedHasher<
            G2Projective,
            ark_ff::field_hashers::DefaultFieldHasher<Sha256>,
            WBMap<<ark_bls12_381::Config as Bls12Config>::G2Config>,
        >,
        G2Projective,
    >(msg);
    let sig = h_m.mul_bigint(sk.0.into_bigint()).into_affine();
    PartialSignature(sig)
}

/// Verify a BLS partial signature.
pub fn partial_verify(
    crs: &GlobalData,
    pk: &PublicKey,
    msg: &[u8],
    partial_sig: &PartialSignature,
) -> bool {
    let g1 = crs.params.powers_of_g[0];
    let h_m = utils::hash_to_g2::<
        MapToCurveBasedHasher<
            G2Projective,
            ark_ff::field_hashers::DefaultFieldHasher<Sha256>,
            WBMap<<ark_bls12_381::Config as Bls12Config>::G2Config>,
        >,
        G2Projective,
    >(msg);
    Curve::pairing(pk.0, h_m) == Curve::pairing(g1, partial_sig.0)
}

/// Aggregate partial signatures and generate the final signature with proof.
pub fn sign_aggregate(
    gd: &GlobalData,
    ak: &AggregationKey,
    threshold: F,
    partial_sigs: &[(usize, PartialSignature)],
    weights: Vec<F>,
    msg: &[u8],
) -> Result<Signature, HintsError> {
    let n = ak.domain_max;
    let mut bitmap = vec![F::zero(); n - 1];
    let mut valid_sigs = Vec::new();
    let mut signer_indices = Vec::new();

    let mut weight_here = F::zero();
    // Verify partial signatures and build bitmap
    for (i, partial_sig) in partial_sigs {
        if *i >= n {
            continue;
        } // Index out of bounds
        if ak.failed_hint_indices.contains(i) {
            continue;
        } // Skip party if hint failed

        let pk = &ak.pks[*i];
        if crate::partial_verify(gd, pk, msg, partial_sig) {
            bitmap[*i] = F::one();
            valid_sigs.push(*partial_sig);
            signer_indices.push(*i);
            weight_here += weights[*i];
        } else {
            // Optional: Log or handle invalid partial signature
        }
    }

    if weight_here < threshold {
        return Err(HintsError::ThresholdNotMet);
    }

    if valid_sigs.is_empty() {
        return Err(HintsError::InvalidInput(
            "No valid partial signatures provided".to_string(),
        ));
    }

    let agg_sig_prime = valid_sigs
        .iter()
        .fold(G2::zero(), |sum, s| (sum + s.0).into_affine())
        .mul_bigint(F::from(n as u64).inverse().unwrap().into_bigint())
        .into_affine();

    let proof = prove(gd, ak, weights, bitmap)?;

    // --- Package Signature ---
    Ok(Signature {
        agg_sig_prime,
        threshold,
        proof,
    })
}

/// Verify: Check the aggregated signature against the threshold and VK.
pub fn verify_aggregate(
    gd: &GlobalData,
    vp: &VerifierKey,
    sig: &Signature,
    msg: &[u8],
) -> Result<bool, HintsError> {
    // 1. Check threshold
    if sig.proof.agg_weight < sig.threshold {
        return Err(HintsError::ThresholdNotMet);
    }

    // 2. Call Internal Verifier (SNARK check)
    // Adapt proof_system::verify signature or call directly
    // It needs vk-like data and the proof parts from sig
    match verify_proof(gd, vp, &sig.proof) {
        Ok(()) => {}
        Err(e) => {
            return Err(HintsError::ProofVerificationError(format!(
                "SNARK failed to verify: {}",
                e
            )))
        }
    }

    // 3. Final BLS Check
    let h_m = utils::hash_to_g2::<
        MapToCurveBasedHasher<
            G2Projective,
            ark_ff::field_hashers::DefaultFieldHasher<Sha256>,
            WBMap<<ark_bls12_381::Config as Bls12Config>::G2Config>,
        >,
        G2Projective,
    >(msg);
    if Curve::pairing(sig.proof.agg_pk, h_m) != Curve::pairing(vp.g_0, sig.agg_sig_prime) {
        return Err(HintsError::BlsVerificationFailed);
    }

    Ok(true)
}

impl AggregationKey {
    pub fn prove(
        &self,
        gd: &GlobalData,
        weights: Vec<F>,
        bitmap: Vec<F>,
    ) -> Result<Proof, HintsError> {
        prove(gd, self, weights, bitmap)
    }

    pub fn aggregate(
        &self,
        gd: &GlobalData,
        threshold: F,
        partial_sigs: &[(usize, PartialSignature)],
        weights: Vec<F>,
        msg: &[u8],
    ) -> Result<Signature, HintsError> {
        crate::sign_aggregate(gd, self, threshold, partial_sigs, weights, msg)
    }
}

impl VerifierKey {
    pub fn verify_aggregate(
        &self,
        gd: &GlobalData,
        sig: &crate::Signature,
        msg: &[u8],
    ) -> Result<bool, HintsError> {
        crate::verify_aggregate(gd, self, sig, msg)
    }
}

#[cfg(test)]
mod test;
