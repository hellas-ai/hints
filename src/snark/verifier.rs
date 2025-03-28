use ark_ec::{pairing::Pairing, CurveGroup};
use ark_ff::Field;
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::ops::*;

use crate::HintsError;

use super::*;

/// Parameters used for verifying proofs.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct VerifierKey {
    pub domain_max: usize, //size of the committee as a power of 2
    pub g_0: G1,           //first element from the KZG SRS over G1
    pub h_0: G2,           //first element from the KZG SRS over G2
    pub h_1: G2,           //2nd element from the KZG SRS over G2
    pub l_n_minus_1_of_x_com: G1,
    pub w_of_x_com: G1,
    pub sk_of_x_com: G2, //commitment to the sigma_{i \in [N]} sk_i l_i(x) polynomial
    pub vanishing_com: G2, //commitment to Z(x) = x^n - 1
    pub x_monomial_com: G2, //commentment to f(x) = x
}

macro_rules! lhs_rhs_eq {
    ($lhs:expr, $rhs:expr) => {
        if $lhs != $rhs {
            return Ok(false);
        }
    };
}

fn verify_opening(
    vp: &VerifierKey,
    commitment: &G1,
    point: &F,
    evaluation: &F,
    opening_proof: &G1,
) -> bool {
    let eval_com: G1 = vp.g_0.clone().mul(evaluation).into();
    let point_com: G2 = vp.h_0.clone().mul(point).into();

    let lhs = <Curve as Pairing>::pairing(commitment.clone() - eval_com, vp.h_0);
    let rhs = <Curve as Pairing>::pairing(opening_proof.clone(), vp.h_1 - point_com);
    lhs == rhs
}

fn verify_openings(vp: &VerifierKey, π: &Proof) -> Result<bool, HintsError> {
    //adjust the w_of_x_com
    let adjustment = F::from(0) - π.agg_weight;
    let adjustment_com = vp.l_n_minus_1_of_x_com.mul(adjustment);
    let w_of_x_com: G1 = (vp.w_of_x_com + adjustment_com).into();

    let psw_of_r_argument = π.psw_of_x_com - vp.g_0.clone().mul(π.psw_of_r).into_affine();
    let w_of_r_argument = w_of_x_com - vp.g_0.clone().mul(π.w_of_r).into_affine();
    let b_of_r_argument = π.b_of_x_com - vp.g_0.clone().mul(π.b_of_r).into_affine();
    let psw_wff_q_of_r_argument =
        π.psw_wff_q_of_x_com - vp.g_0.clone().mul(π.psw_wff_q_of_r).into_affine();
    let psw_check_q_of_r_argument =
        π.psw_check_q_of_x_com - vp.g_0.clone().mul(π.psw_check_q_of_r).into_affine();
    let b_wff_q_of_r_argument =
        π.b_wff_q_of_x_com - vp.g_0.clone().mul(π.b_wff_q_of_r).into_affine();
    let b_check_q_of_r_argument =
        π.b_check_q_of_x_com - vp.g_0.clone().mul(π.b_check_q_of_r).into_affine();

    let merged_argument: G1 = (psw_of_r_argument
        + w_of_r_argument.mul(π.r.pow([1]))
        + b_of_r_argument.mul(π.r.pow([2]))
        + psw_wff_q_of_r_argument.mul(π.r.pow([3]))
        + psw_check_q_of_r_argument.mul(π.r.pow([4]))
        + b_wff_q_of_r_argument.mul(π.r.pow([5]))
        + b_check_q_of_r_argument.mul(π.r.pow([6])))
    .into_affine();

    let lhs = <Curve as Pairing>::pairing(merged_argument, vp.h_0);
    let rhs = <Curve as Pairing>::pairing(
        π.merged_proof,
        vp.h_1 - vp.h_0.clone().mul(π.r).into_affine(),
    );

    lhs_rhs_eq!(lhs, rhs);

    let domain = Radix2EvaluationDomain::<F>::new(vp.domain_max as usize)
        .ok_or(HintsError::PolynomialDegreeTooLarge)?;
    let ω: F = domain.group_gen;
    let r_div_ω: F = π.r / ω;
    Ok(verify_opening(
        vp,
        &π.psw_of_x_com,
        &r_div_ω,
        &π.psw_of_r_div_ω,
        &π.psw_of_r_div_ω_proof,
    ))
}

/// Verify a proof for an aggregated signature.
pub fn verify_proof(vp: &VerifierKey, π: &Proof) -> Result<bool, HintsError> {
    let domain = Radix2EvaluationDomain::<F>::new(vp.domain_max as usize)
        .ok_or(HintsError::PolynomialDegreeTooLarge)?;
    let ω: F = domain.group_gen;

    if let false = verify_openings(vp, π)? {
        return Ok(false);
    }

    let n: u64 = vp.domain_max as u64;
    let vanishing_of_r: F = π.r.pow([n]) - F::from(1);

    // compute L_i(r) using the relation L_i(x) = Z_V(x) / ( Z_V'(x) (x - ω^i) )
    // where Z_V'(x)^-1 = x / N for N = |V|.
    let ω_pow_n_minus_1 = ω.pow([n - 1]);
    let l_n_minus_1_of_r =
        (ω_pow_n_minus_1 / F::from(n)) * (vanishing_of_r / (π.r - ω_pow_n_minus_1));

    //assert polynomial identity for the secret part
    let lhs = <Curve as Pairing>::pairing(&π.b_of_x_com, &vp.sk_of_x_com);
    let x1 = <Curve as Pairing>::pairing(&π.sk_q1_com, &vp.vanishing_com);
    let x2 = <Curve as Pairing>::pairing(&π.sk_q2_com, &vp.x_monomial_com);
    let x3 = <Curve as Pairing>::pairing(&π.agg_pk, &vp.h_0);
    let rhs = x1.add(x2).add(x3);
    lhs_rhs_eq!(lhs, rhs);

    //assert checks on the public part

    //ParSumW(r) − ParSumW(r/ω) − W(r) · b(r) = Q(r) · (r^n − 1)
    let lhs = π.psw_of_r - π.psw_of_r_div_ω - π.w_of_r * π.b_of_r;
    let rhs = π.psw_wff_q_of_r * vanishing_of_r;
    lhs_rhs_eq!(lhs, rhs);

    //Ln−1(X) · ParSumW(X) = Z(X) · Q2(X)
    //TODO: compute l_n_minus_1_of_r in verifier -- dont put it in the proof.
    let lhs = l_n_minus_1_of_r * π.psw_of_r;
    let rhs = vanishing_of_r * π.psw_check_q_of_r;
    lhs_rhs_eq!(lhs, rhs);

    //b(r) * b(r) - b(r) = Q(r) · (r^n − 1)
    let lhs = π.b_of_r * π.b_of_r - π.b_of_r;
    let rhs = π.b_wff_q_of_r * vanishing_of_r;
    lhs_rhs_eq!(lhs, rhs);

    //Ln−1(X) · (b(X) − 1) = Z(X) · Q4(X)
    let lhs = l_n_minus_1_of_r * (π.b_of_r - F::from(1));
    let rhs = vanishing_of_r * π.b_check_q_of_r;
    lhs_rhs_eq!(lhs, rhs);

    Ok(true)
}
