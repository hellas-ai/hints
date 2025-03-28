#![allow(dead_code)]

use ark_ec::{hashing::HashToCurve, pairing::Pairing, CurveGroup};
use ark_ff::{Field /* FftField */};
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, Evaluations, Polynomial, Radix2EvaluationDomain,
};

use crate::HintsError;
//use ark_std::{UniformRand, test_rng, ops::*};
type F = <crate::snark::Curve as Pairing>::ScalarField;

//returns t(X) = X^n - 1
pub fn compute_vanishing_poly(n: usize) -> DensePolynomial<F> {
    let mut coeffs = vec![];
    for i in 0..n + 1 {
        if i == 0 {
            coeffs.push(F::from(0) - F::from(1)); // -1
        } else if i == n {
            coeffs.push(F::from(1)); // X^n
        } else {
            coeffs.push(F::from(0));
        }
    }
    DensePolynomial { coeffs }
}

// 1 at omega^i and 0 elsewhere on domain {omega^i}_{i \in [n]}
pub fn lagrange_poly(domain_max: usize, i: usize) -> DensePolynomial<F> {
    //todo: check n is a power of 2
    let mut evals = vec![];
    for j in 0..domain_max {
        let l_of_x: u64 = if i == j { 1 } else { 0 };
        evals.push(F::from(l_of_x));
    }

    //powers of nth root of unity
    let domain = Radix2EvaluationDomain::<F>::new(domain_max).unwrap();
    let eval_form = Evaluations::from_vec_and_domain(evals, domain);
    //interpolated polynomial over the n points
    eval_form.interpolate()
}

// returns t(X) = X
pub fn compute_x_monomial() -> DensePolynomial<F> {
    let mut coeffs = vec![];
    coeffs.push(F::from(0)); // 0
    coeffs.push(F::from(1)); // X
    DensePolynomial { coeffs }
}

// returns t(X) = c
pub fn compute_constant_poly(c: &F) -> DensePolynomial<F> {
    let mut coeffs = vec![];
    coeffs.push(c.clone()); // c
    DensePolynomial { coeffs }
}

//computes f(ωx)
pub fn poly_domain_mult_ω(f: &DensePolynomial<F>, ω: &F) -> DensePolynomial<F> {
    let mut new_poly = f.clone();
    for i in 1..(f.degree() + 1) {
        //we don't touch the zeroth coefficient
        let ω_pow_i: F = ω.pow([i as u64]);
        new_poly.coeffs[i] = new_poly.coeffs[i] * ω_pow_i;
    }
    new_poly
}

//computes c . f(x), for some constnt c
pub fn poly_eval_mult_c(f: &DensePolynomial<F>, c: &F) -> DensePolynomial<F> {
    let mut new_poly = f.clone();
    for i in 0..(f.degree() + 1) {
        new_poly.coeffs[i] = new_poly.coeffs[i] * c.clone();
    }
    new_poly
}

pub(crate) fn compute_poly(
    v: &Vec<F>,
    aug: &F,
    domain_max: usize,
) -> Result<DensePolynomial<F>, HintsError> {
    if v.len() != domain_max - 1 {
        return Err(HintsError::InvalidInput(format!(
            "compute_poly: Input vector length {} does not match n-1 ({})",
            v.len(),
            domain_max - 1
        )));
    }
    let mut evals = Vec::with_capacity(domain_max);
    evals.extend_from_slice(v);
    evals.push(*aug);

    let domain =
        Radix2EvaluationDomain::<F>::new(domain_max).ok_or(HintsError::PolynomialDegreeTooLarge)?;
    let eval_form = Evaluations::from_vec_and_domain(evals, domain);
    Ok(eval_form.interpolate())
}

pub(crate) fn compute_psw_poly(
    weights: &[F], // len n-1
    bitmap: &[F],  // len n-1
    weight_aug: &F,
    bitmap_aug: &F,
    domain_max: usize,
) -> Result<DensePolynomial<F>, HintsError> {
    if weights.len() != domain_max - 1 || bitmap.len() != domain_max - 1 {
        return Err(HintsError::InvalidInput(format!(
            "compute_psw_poly: Input vector lengths ({}, {}) do not match n-1 ({})",
            weights.len(),
            bitmap.len(),
            domain_max - 1
        )));
    }

    let mut parsum = F::from(0);
    let mut evals = Vec::with_capacity(domain_max);
    for i in 0..(domain_max - 1) {
        // Iterate up to n-1
        let w_i_b_i = bitmap[i] * weights[i];
        parsum += w_i_b_i;
        evals.push(parsum);
    }
    // Add evaluation for the augmented element (at index n-1)
    parsum += bitmap_aug * weight_aug;
    evals.push(parsum); // Now evals has length n

    let domain =
        Radix2EvaluationDomain::<F>::new(domain_max).ok_or(HintsError::PolynomialDegreeTooLarge)?; // Use n here
    let eval_form = Evaluations::from_vec_and_domain(evals, domain);
    Ok(eval_form.interpolate())
}

pub(crate) fn hash_to_g2<H: HashToCurve<G>, G: CurveGroup>(msg: &[u8]) -> G::Affine {
    let hasher = H::new(b"hints BLS12-381 signature").unwrap();
    hasher.hash(msg).unwrap()
}
