use hints::{snark::F, utils};

use ark_ff::{Field, UniformRand};
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Polynomial,
    Radix2EvaluationDomain,
};
use ark_std::{ops::*, test_rng, One, Zero};

mod test_helpers;

fn test_poly_domain_mult(f_of_x: &DensePolynomial<F>, f_of_ωx: &DensePolynomial<F>, ω: &F) {
    let mut rng = test_rng();
    let r = F::rand(&mut rng);
    let ωr = *ω * r;
    assert_eq!(f_of_x.evaluate(&ωr), f_of_ωx.evaluate(&r));
}

#[test]
fn test_polynomial_degree_preservation() {
    // Test that operations preserve expected polynomial degrees
    let weights: Vec<F> = vec![F::from(2), F::from(3), F::from(4)];
    let weight_aug = F::from(0);
    let bitmap: Vec<F> = vec![F::from(1), F::from(1), F::from(0)];
    let bitmap_aug = F::from(1);
    let n = bitmap.len() + 1;

    let w_of_x = utils::compute_poly(&weights, &weight_aug, n).unwrap();
    let b_of_x = utils::compute_poly(&bitmap, &bitmap_aug, n).unwrap();

    // Check degrees
    assert_eq!(
        w_of_x.degree(),
        n - 1,
        "Weight polynomial degree should be n-1"
    );
    assert_eq!(
        b_of_x.degree(),
        n - 1,
        "Bitmap polynomial degree should be n-1"
    );

    // Test multiplication degree
    let product = w_of_x.clone().mul(&b_of_x);
    assert_eq!(
        product.degree(),
        w_of_x.degree() + b_of_x.degree(),
        "Product degree should be sum of individual degrees"
    );
}

#[test]
fn test_polynomial_evaluation_agreement() {
    // Test that polynomial evaluation at points matches expected values
    let weights: Vec<F> = vec![F::from(2), F::from(3), F::from(4)];
    let weight_aug = F::from(5);
    let n = weights.len() + 1;

    let w_of_x = utils::compute_poly(&weights, &weight_aug, n).unwrap();

    // Test evaluation at domain points
    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let omega = domain.group_gen;

    // Check that polynomial evaluates to correct values at domain points
    for (i, weight) in weights.iter().enumerate() {
        let point = omega.pow([(i + 1) as u64]);
        let evaluation = w_of_x.evaluate(&point);
        assert_eq!(
            evaluation,
            *weight,
            "Polynomial should evaluate to the correct weight at domain point {}",
            i + 1
        );
    }

    // Check augmented point
    let aug_point = F::one(); // ω^n = 1
    let aug_evaluation = w_of_x.evaluate(&aug_point);
    assert_eq!(
        aug_evaluation, weight_aug,
        "Polynomial should evaluate to augmented weight at point 1"
    );
}

#[test]
fn test_domain_multiplication() {
    // Test that domain multiplication works correctly
    let weights: Vec<F> = vec![F::from(2), F::from(3), F::from(4), F::from(5)];
    let weight_aug = F::from(0);
    let n = weights.len() + 1;

    let w_of_x = utils::compute_poly(&weights, &weight_aug, n).unwrap();

    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let ω = domain.group_gen;

    let w_of_ωx = utils::poly_domain_mult_ω(&w_of_x, &ω);

    // Verify the transformation
    test_poly_domain_mult(&w_of_x, &w_of_ωx, &ω);

    // Additionally check specific points
    let r = F::from(42); // Some arbitrary point
    let w_r = w_of_x.evaluate(&r);
    let w_ωr = w_of_ωx.evaluate(&r);

    // Also check w_of_ωx directly using the original polynomial
    let ωr = ω * r;
    let w_ωr_direct = w_of_x.evaluate(&ωr);

    assert_eq!(
        w_ωr, w_ωr_direct,
        "Domain multiplication should correctly transform evaluation points"
    );
}

#[test]
fn test_vanishing_polynomial() {
    // Test properties of the vanishing polynomial Z(X) = X^n - 1

    let n = 8;
    let z_of_x = utils::compute_vanishing_poly(n);

    // Check degree
    assert_eq!(
        z_of_x.degree(),
        n,
        "Vanishing polynomial should have degree n"
    );

    // Check that it vanishes on all nth roots of unity
    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let ω = domain.group_gen;

    for i in 0..n {
        let point = ω.pow([i as u64]);
        let eval = z_of_x.evaluate(&point);
        assert!(
            eval.is_zero(),
            "Vanishing polynomial should be zero at {}th root of unity",
            i
        );
    }

    // Check that it's non-zero outside domain
    let non_root = F::from(42);
    let eval_non_root = z_of_x.evaluate(&non_root);
    assert!(
        !eval_non_root.is_zero(),
        "Vanishing polynomial should be non-zero outside the domain"
    );
}

#[test]
fn test_lagrange_polynomials() {
    // Test properties of Lagrange polynomials

    let n = 8;
    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let ω = domain.group_gen;

    // For each index, create the Lagrange polynomial and test its properties
    for i in 0..n {
        let l_i = utils::lagrange_poly(n, i);

        // Check that l_i(ω^j) = 1 if i=j, 0 otherwise
        for j in 0..n {
            let point = ω.pow([j as u64]);
            let eval = l_i.evaluate(&point);

            if i == j {
                assert_eq!(
                    eval,
                    F::one(),
                    "Lagrange polynomial l_{} should be 1 at point ω^{}",
                    i,
                    j
                );
            } else {
                assert!(
                    eval.is_zero(),
                    "Lagrange polynomial l_{} should be 0 at point ω^{}",
                    i,
                    j
                );
            }
        }
    }
}

#[test]
fn test_polynomial_division() {
    // Test polynomial division correctness

    let n = 8;
    let z_of_x = utils::compute_vanishing_poly(n); // X^n - 1

    // Create a polynomial that's divisible by Z(X)
    let mut rng = test_rng();
    let quotient_degree = 3;
    let quotient_coeffs: Vec<F> = (0..=quotient_degree).map(|_| F::rand(&mut rng)).collect();
    let quotient = DensePolynomial::from_coefficients_vec(quotient_coeffs);

    // Multiply to get a polynomial divisible by Z(X)
    let product = quotient.clone().mul(&z_of_x);

    // Now divide and check that we get back the quotient
    let result = product.div(&z_of_x);

    assert_eq!(
        result.degree(),
        quotient.degree(),
        "Division result should have same degree as original quotient"
    );

    assert_eq!(
        result, quotient,
        "Division should recover the original quotient polynomial"
    );
}
