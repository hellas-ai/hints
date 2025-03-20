use std::time::Instant;

use ark_bls12_381::Bls12_381;
use ark_ec::VariableBaseMSM;
use ark_ec::{pairing::Pairing, CurveGroup};
use ark_ff::{Field /* FftField */};
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, Evaluations, Polynomial, Radix2EvaluationDomain,
};
use ark_std::rand::Rng;
use ark_std::{ops::*, test_rng, UniformRand};

use super::*;
use super::proof_system::*;

fn aggregate_sk(sk: &Vec<F>, bitmap: &Vec<F>) -> F {
    let n = sk.len();
    let mut agg_sk = F::from(0);
    for i in 0..sk.len() {
        let l_i_of_x = utils::lagrange_poly(n, i);
        let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
        agg_sk += bitmap[i] * sk[i] * l_i_of_0;
    }
    agg_sk
}

fn sanity_test_poly_domain_mult(
    f_of_x: &DensePolynomial<F>, f_of_ωx: &DensePolynomial<F>, ω: &F
) {
    let mut rng = test_rng();
    let r = F::rand(&mut rng);
    let ωr: F = ω.clone() * r;
    assert_eq!(f_of_x.evaluate(&ωr), f_of_ωx.evaluate(&r));
}

fn sanity_test_b(b_of_x: &DensePolynomial<F>, q_of_x: &DensePolynomial<F>) {
    let mut rng = test_rng();
    let r = F::rand(&mut rng);

    let n: u64 = (b_of_x.degree() + 1) as u64;

    let b_of_r = b_of_x.evaluate(&r);
    let q_of_r = q_of_x.evaluate(&r);
    let vanishing_of_r: F = r.pow([n]) - F::from(1);

    //ParSumW(ωr) − ParSumW(r) − W(ωr) · b(ωr) = Q2(r) · (r^n − 1)
    let left = b_of_r * b_of_r - b_of_r;
    let right = q_of_r * vanishing_of_r;
    //println!("ParSumW(ωr) - ParSumW(r) - W(ωr)·b(ωr) = {:?}", tmp1);
    //println!("Q(r) · (r^n - 1) = {:?}", tmp2);
    assert_eq!(left, right);
}

fn sanity_test_psw(
    w_of_x: &DensePolynomial<F>,
    b_of_x: &DensePolynomial<F>,
    psw_of_x: &DensePolynomial<F>,
    q_of_x: &DensePolynomial<F>,
) {
    let mut rng = test_rng();
    let r = F::rand(&mut rng);

    let n: u64 = (b_of_x.degree() + 1) as u64;
    let domain = Radix2EvaluationDomain::<F>::new(n as usize).unwrap();
    let ω: F = domain.group_gen;
    let ω_pow_n_minus_1: F = ω.pow([n - 1]);
    let ωr: F = ω * r;

    let psw_of_r = psw_of_x.evaluate(&r);
    let psw_of_ωr = psw_of_x.evaluate(&ωr);
    let w_of_ωr = w_of_x.evaluate(&ωr);
    let b_of_ωr = b_of_x.evaluate(&ωr);
    let q_of_r = q_of_x.evaluate(&r);
    let vanishing_of_r: F = r.pow([n]) - F::from(1);

    //ParSumW(ωr) − ParSumW(r) − W(ωr) · b(ωr) = Q2(r) · (r^n − 1)
    let tmp1 = psw_of_ωr - psw_of_r - w_of_ωr * b_of_ωr;
    let tmp2 = q_of_r * vanishing_of_r;
    //println!("ParSumW(ωr) - ParSumW(r) - W(ωr)·b(ωr) = {:?}", tmp1);
    //println!("Q(r) · (r^n - 1) = {:?}", tmp2);
    assert_eq!(tmp1, tmp2);

    //ParSumW(ωn−1) = 0
    let psw_of_ω_pow_n_minus_1 = psw_of_x.evaluate(&ω_pow_n_minus_1);
    //println!("ParSumW(ω^(n-1)) = {:?}", psw_of_ω_pow_n_minus_1);
    assert_eq!(psw_of_ω_pow_n_minus_1, F::from(0));

    //b(ωn−1) = 1
    let b_of_ω_pow_n_minus_1 = b_of_x.evaluate(&ω_pow_n_minus_1);
    assert_eq!(b_of_ω_pow_n_minus_1, F::from(1));
}

#[test]
fn sanity_test_public_part() {
    // compute the nth root of unity
    //println!("The nth root of unity is: {:?}", ω);
    //println!("The omega_n_minus_1 of unity is: {:?}", ω.pow([n-1]));
    //println!("The omega_n of unity is: {:?}", ω_pow_n_minus_1 * ω);

    let weights: Vec<F> = vec![
        F::from(2),
        F::from(3),
        F::from(4),
        F::from(5),
        F::from(4),
        F::from(3),
        F::from(2),
        F::from(0) - F::from(15),
    ];
    let bitmap: Vec<F> = vec![
        F::from(1),
        F::from(1),
        F::from(0),
        F::from(1),
        F::from(0),
        F::from(1),
        F::from(1),
        F::from(1),
    ];

    let n: u64 = bitmap.len() as u64;
    let domain = Radix2EvaluationDomain::<F>::new(n as usize).unwrap();
    let ω: F = domain.group_gen;

    let w_of_x = compute_poly(&weights);
    let w_of_ωx = utils::poly_domain_mult_ω(&w_of_x, &ω);

    let b_of_x = compute_poly(&bitmap);
    let b_of_ωx = utils::poly_domain_mult_ω(&b_of_x, &ω);

    let psw_of_x = compute_psw_poly(&weights, &bitmap);
    let psw_of_ωx = utils::poly_domain_mult_ω(&psw_of_x, &ω);

    //t(X) = ParSumW(ω · X) − ParSumW(X) − W(ω · X) · b(ω · X)
    let t_of_x = psw_of_ωx
        .clone()
        .sub(&psw_of_x)
        .sub(&w_of_ωx.clone().mul(&b_of_ωx));
    let z_of_x = utils::compute_vanishing_poly(n as usize); //returns Z(X) = X^n - 1
    let q2_of_x = t_of_x.div(&z_of_x);

    let t_of_x = b_of_x.clone().mul(&b_of_x).sub(&b_of_x);
    let q1_of_x = t_of_x.div(&z_of_x);

    sanity_test_poly_domain_mult(&w_of_x, &w_of_ωx, &ω);
    sanity_test_poly_domain_mult(&b_of_x, &b_of_ωx, &ω);
    sanity_test_poly_domain_mult(&psw_of_x, &psw_of_ωx, &ω);

    sanity_test_psw(&w_of_x, &b_of_x, &psw_of_x, &q2_of_x);
    sanity_test_b(&b_of_x, &q1_of_x);
}

fn sanity_test_pssk(
    sk_of_x: &DensePolynomial<F>,
    b_of_x: &DensePolynomial<F>,
    q1_of_x: &DensePolynomial<F>,
    q2_of_x: &DensePolynomial<F>,
    agg_sk: &F,
) {
    let mut rng = test_rng();
    let r = F::rand(&mut rng);
    let n: u64 = (sk_of_x.degree() + 1) as u64;

    //SK(x) · B(x) − aSK = Q1(x) · Z(x) + Q2(x) · x
    let sk_of_r = sk_of_x.evaluate(&r);
    let b_of_r = b_of_x.evaluate(&r);
    let q1_of_r = q1_of_x.evaluate(&r);
    let z_of_r: F = r.pow([n]) - F::from(1);
    let q2_of_r = q2_of_x.evaluate(&r);

    let left = sk_of_r * b_of_r;
    let right = (q1_of_r * z_of_r) + (q2_of_r * r) + agg_sk;
    assert_eq!(left, right);
}

#[test]
fn sanity_test_secret_part() {
    //let weights: Vec<u64> = vec![2, 3, 4, 5, 4, 3, 2];
    let bitmap: Vec<F> = vec![
        F::from(1),
        F::from(1),
        F::from(0),
        F::from(1),
        F::from(0),
        F::from(1),
        F::from(1),
        F::from(1),
    ];

    let n = bitmap.len();

    let mut secret_keys: Vec<F> = sample_secret_keys(n - 1);
    secret_keys.push(F::from(0));

    let agg_sk = aggregate_sk(&secret_keys, &bitmap);
    println!("agg_sk = {:?}", agg_sk);
    let sk_of_x = compute_poly(&secret_keys);
    let b_of_x = compute_poly(&bitmap);
    let q1_of_x = compute_pssk_q1_poly(&secret_keys, &bitmap);
    let q2_of_x = compute_pssk_q2_poly(&secret_keys, &bitmap);

    sanity_test_pssk(&sk_of_x, &b_of_x, &q1_of_x, &q2_of_x, &agg_sk);
}

fn compute_pssk_q1_poly(sk: &Vec<F>, bitmap: &Vec<F>) -> DensePolynomial<F> {
    let n = sk.len();
    let z_of_x = utils::compute_vanishing_poly(n);
    //Li(x) · Li(x) − Li(x) / Z(x)
    let mut q1 = utils::compute_constant_poly(&F::from(0));

    for i in 0..n {
        if bitmap[i] == F::from(0) {
            continue;
        }

        let l_i_of_x = utils::lagrange_poly(n, i);
        let num = l_i_of_x.clone().mul(&l_i_of_x).sub(&l_i_of_x);
        //let num = num.sub(&l_i_of_x);
        let f_i = num.div(&z_of_x);
        let sk_i_f_i = utils::poly_eval_mult_c(&f_i, &sk[i]);

        q1 = q1.add(sk_i_f_i);

        let mut q1_inner = utils::compute_constant_poly(&F::from(0));
        for j in 0..n {
            if i == j {
                continue;
            } //i != j

            let l_j_of_x = utils::lagrange_poly(n, j);
            let num = l_j_of_x.mul(&l_i_of_x);
            let f_j = num.div(&z_of_x);
            let sk_j_f_j = utils::poly_eval_mult_c(&f_j, &sk[j]);

            q1_inner = q1_inner.add(sk_j_f_j);
        }

        q1 = q1.add(q1_inner);
    }
    q1
}

fn compute_pssk_q2_poly(sk: &Vec<F>, bitmap: &Vec<F>) -> DensePolynomial<F> {
    let n = sk.len();
    let x_monomial = utils::compute_x_monomial();

    let mut q2 = utils::compute_constant_poly(&F::from(0));

    for i in 0..n {
        if bitmap[i] == F::from(0) {
            continue;
        }

        let l_i_of_x = utils::lagrange_poly(n, i);
        let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
        let l_i_of_0 = utils::compute_constant_poly(&l_i_of_0);
        let num = l_i_of_x.sub(&l_i_of_0);
        let den = x_monomial.clone();
        let f_i = num.div(&den);
        let sk_i_f_i = utils::poly_eval_mult_c(&f_i, &sk[i]);

        q2 = q2.add(sk_i_f_i);
    }
    q2
}
