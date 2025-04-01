use ark_ec::CurveGroup;
use ark_ff::Field;
use ark_poly::{EvaluationDomain, Polynomial, Radix2EvaluationDomain};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{ops::*, Zero};

use crate::{HintsError, PublicKey};

use super::*;

/// SNARK proof certifying the validity of an aggregated signature.
#[derive(Clone, Debug, Default, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof {
    pub agg_pk: G1,
    pub agg_weight: F,

    pub r: F,

    pub merged_proof: G1,

    pub psw_of_r: F,

    pub psw_of_r_div_ω: F,
    pub psw_of_r_div_ω_proof: G1,
    pub w_of_r: F,
    pub b_of_r: F,
    pub psw_wff_q_of_r: F,
    pub psw_check_q_of_r: F,
    pub b_wff_q_of_r: F,
    pub b_check_q_of_r: F,

    pub coms: ProofCommitments,
}

/// Parameters used for aggregating proofs.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct AggregationKey {
    pub domain_max: usize,
    pub pks: Vec<PublicKey>, //g^sk_i for each party i
    pub weights: Vec<F>,
    pub q1_coms: Vec<G1>,    //preprocessed contributions for pssk_q1
    pub q2_coms: Vec<G1>,    //preprocessed contributions for pssk_q2
    pub failed_hint_indices: Vec<usize>,
    // Add commitments from VerifierKey needed for FS transcript consistency
    pub vk_l_n_minus_1_com: G1,
    pub vk_w_of_x_com: G1,
    pub vk_sk_of_x_com: G2,
    pub vk_vanishing_com: G2,
    pub vk_x_monomial_com: G2,
}

/// Prove a proof for an aggregated signature.
pub fn prove(
    gd: &GlobalData,
    ak: &AggregationKey,
    weights: &[F],
    bitmap: &[F],
) -> Result<Proof, HintsError> {
    // compute the nth root of unity
    let n = gd.domain_max;
    let params = &gd.params;

    if weights.len() != n - 1 || bitmap.len() != n - 1 {
        return Err(HintsError::InvalidInput(format!(
            "prove: Input vector lengths ({}, {}) do not match n-1 ({})",
            weights.len(),
            bitmap.len(),
            n - 1
        )));
    }

    //compute sum of weights of active signers
    // doesn't include aug, because bit(1) * weight(0) = 0.
    let total_active_weight = bitmap
        .iter()
        .zip(weights.iter())
        .fold(F::from(0), |acc, (&x, &y)| acc + (x * y));

    //weight's last element must the additive inverse of active weight
    let weight_aug = F::from(0) - total_active_weight;

    //bitmap's last element must be 1 for our scheme
    let bitmap_aug = F::from(1);

    //compute all the scalars we will need in the prover
    let domain = Radix2EvaluationDomain::<F>::new(n).ok_or(HintsError::PolynomialDegreeTooLarge)?;
    let ω: F = domain.group_gen;
    let ω_inv: F = F::from(1) / ω;

    //compute all the polynomials we will need in the prover (degree n-1)
    let z_of_x = utils::compute_vanishing_poly(n); // X^n - 1
    let l_n_minus_1_of_x = utils::lagrange_poly(n, n - 1); // Uses domain size n
    let w_of_x = utils::compute_poly(weights, &weight_aug, n)?;
    let b_of_x = utils::compute_poly(bitmap, &bitmap_aug, n)?;
    let psw_of_x = utils::compute_psw_poly(weights, bitmap, &weight_aug, &bitmap_aug, n)?;
    let psw_of_x_div_ω = utils::poly_domain_mult_ω(&psw_of_x, &ω_inv);

    // Compute quotient polynomials
    let t_of_x_1 = &psw_of_x - &psw_of_x_div_ω - (&w_of_x * &b_of_x);
    let psw_wff_q_of_x = &t_of_x_1 / &z_of_x;

    let t_of_x_2 = &l_n_minus_1_of_x * &psw_of_x;
    let psw_check_q_of_x = &t_of_x_2 / &z_of_x;

    let t_of_x_3 = &b_of_x * &b_of_x - &b_of_x;
    let b_wff_q_of_x = &t_of_x_3 / &z_of_x;

    let const_one_poly = utils::compute_constant_poly(&F::from(1));
    let t_of_x_4 = &l_n_minus_1_of_x * (&b_of_x - &const_one_poly);
    let b_check_q_of_x = &t_of_x_4 / &z_of_x;

    // --- Create the FULL n-element bitmap and pk list for filtering/apk ---
    let mut bitmap_full = bitmap.to_vec(); // Starts with n-1 elements
    bitmap_full.push(bitmap_aug); // Add the n-th element (which is 1)

    let pk_aug = PublicKey((params.powers_of_g[0] * F::zero()).into_affine()); // Identity/Zero Point
    let mut pks_full = ak.pks.clone(); // Starts with n-1 pks
    pks_full.push(pk_aug); // Add the n-th pk

    // --- Use the full bitmap for filtering ---
    // ak.q1_coms and ak.q2_coms already have length n
    let sk_q1_com = filter_and_add(params, &ak.q1_coms, &bitmap_full);
    let sk_q2_com = filter_and_add(params, &ak.q2_coms, &bitmap_full);

    // --- Use the full pk list and full bitmap for agg_pk ---
    // cache.lagrange_polynomials should have length n
    let agg_pk = compute_apk(&pks_full, &gd.lagrange_polynomials, &bitmap_full);

    // Commit to polynomials (prover's first round messages)
    let psw_of_x_com = KZG::commit_g1(params, &psw_of_x)?;
    let b_of_x_com = KZG::commit_g1(params, &b_of_x)?;
    let psw_wff_q_of_x_com = KZG::commit_g1(params, &psw_wff_q_of_x)?;
    let psw_check_q_of_x_com = KZG::commit_g1(params, &psw_check_q_of_x)?;
    let b_wff_q_of_x_com = KZG::commit_g1(params, &b_wff_q_of_x)?;
    let b_check_q_of_x_com = KZG::commit_g1(params, &b_check_q_of_x)?;

    // --- Fiat-Shamir: Compute challenge r ---
    let commitments = ProofCommitments {
        psw_of_x_com,
        b_of_x_com,
        psw_wff_q_of_x_com,
        psw_check_q_of_x_com,
        b_wff_q_of_x_com,
        b_check_q_of_x_com,
        sk_q1_com,
        sk_q2_com,
    };

    let r = compute_challenge_r(
        &gd.lockstitch,
        ak, // AggregationKey implements FiatShamirTranscriptData
        &agg_pk,
        &total_active_weight,
        &commitments,
    )?;
    let r_div_ω: F = r / ω;
    // --- End Fiat-Shamir ---

    // --- Compute Opening Proofs ---
    let psw_of_r_proof = KZG::compute_opening_proof(params, &psw_of_x, &r)?;
    let w_of_r_proof = KZG::compute_opening_proof(params, &w_of_x, &r)?;
    let b_of_r_proof = KZG::compute_opening_proof(params, &b_of_x, &r)?;
    let psw_wff_q_of_r_proof = KZG::compute_opening_proof(params, &psw_wff_q_of_x, &r)?;
    let psw_check_q_of_r_proof = KZG::compute_opening_proof(params, &psw_check_q_of_x, &r)?;
    let b_wff_q_of_r_proof = KZG::compute_opening_proof(params, &b_wff_q_of_x, &r)?;
    let b_check_q_of_r_proof = KZG::compute_opening_proof(params, &b_check_q_of_x, &r)?;
    let psw_of_r_div_omega_proof = KZG::compute_opening_proof(params, &psw_of_x, &r_div_ω)?; // Renamed

    // --- Batch Openings (Merge Proofs) ---
    // Note: Powers match the paper's definition (0-indexed) and Plonk batching
    let merged_proof: G1 = (psw_of_r_proof                  // y^0
        + w_of_r_proof.mul(r.pow([1]))        // y^1
        + b_of_r_proof.mul(r.pow([2]))        // y^2
        + psw_wff_q_of_r_proof.mul(r.pow([3]))// y^3
        + psw_check_q_of_r_proof.mul(r.pow([4]))// y^4
        + b_wff_q_of_r_proof.mul(r.pow([5]))  // y^5
        + b_check_q_of_r_proof.mul(r.pow([6]))) // y^6
    .into(); // Convert G1Projective to G1Affine if needed, depends on Mul impl

    Ok(Proof {
        agg_pk,
        agg_weight: total_active_weight,
        r,
        psw_of_r_div_ω: psw_of_x.evaluate(&r_div_ω),
        psw_of_r_div_ω_proof: psw_of_r_div_omega_proof, // Use renamed proof
        psw_of_r: psw_of_x.evaluate(&r),
        w_of_r: w_of_x.evaluate(&r),
        b_of_r: b_of_x.evaluate(&r),
        psw_wff_q_of_r: psw_wff_q_of_x.evaluate(&r),
        psw_check_q_of_r: psw_check_q_of_x.evaluate(&r),
        b_wff_q_of_r: b_wff_q_of_x.evaluate(&r),
        b_check_q_of_r: b_check_q_of_x.evaluate(&r),
        merged_proof, // Ensure it's Affine
        coms: commitments,
    })
}