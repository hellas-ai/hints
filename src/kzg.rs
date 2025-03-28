//adapted from https://github.com/arkworks-rs/poly-commit/blob/master/src/kzg10/mod.rs
#![allow(dead_code)]
#![allow(unused_imports)]

//use ark_ec::AffineRepr;
use ark_ec::{pairing::Pairing, CurveGroup};
use ark_ec::{
    scalar_mul::{BatchMulPreprocessing, ScalarMul},
    VariableBaseMSM,
};
use ark_ff::{One, PrimeField, UniformRand, Zero};
use ark_poly::DenseUVPolynomial;
use ark_std::{format, marker::PhantomData, ops::*, vec};

use ark_std::rand::RngCore;
#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub struct KZG10<E: Pairing, P: DenseUVPolynomial<E::ScalarField>> {
    _engine: PhantomData<E>,
    _poly: PhantomData<P>,
}

pub struct UniversalParams<E: Pairing> {
    /// Group elements of the form `{ \beta^i G }`, where `i` ranges from 0 to `degree`.
    pub powers_of_g: Vec<E::G1Affine>,
    /// Group elements of the form `{ \beta^i H }`, where `i` ranges from 0 to `degree`.
    pub powers_of_h: Vec<E::G2Affine>,
}

#[derive(Debug)]
pub enum Error {
    /// The degree provided in setup was too small; degree 0 polynomials
    /// are not supported.
    DegreeIsZero,

    /// The degree of the polynomial passed to `commit` or `open`
    /// was too large.
    TooManyCoefficients {
        /// The number of coefficients in the polynomial.
        num_coefficients: usize,
        /// The maximum number of powers provided in `Powers`.
        num_powers: usize,
    },
}

impl<E, P> KZG10<E, P>
where
    E: Pairing,
    P: DenseUVPolynomial<E::ScalarField, Point = E::ScalarField>,
    for<'a, 'b> &'a P: Div<&'b P, Output = P>,
    for<'a, 'b> &'a P: Sub<&'b P, Output = P>,
{
    pub fn setup<R: RngCore>(max_degree: usize, rng: &mut R) -> Result<UniversalParams<E>, Error> {
        if max_degree < 1 {
            return Err(Error::DegreeIsZero);
        }

        //let setup_time = start_timer!(|| format!("KZG10::Setup with degree {}", max_degree));
        let beta = E::ScalarField::rand(rng);
        let g = E::G1::rand(rng);
        let h = E::G2::rand(rng);

        let mut powers_of_beta = vec![E::ScalarField::one()];

        let mut cur = beta;
        for _ in 0..max_degree {
            powers_of_beta.push(cur);
            cur *= &beta;
        }

        let g_table = BatchMulPreprocessing::new(g, max_degree);
        let powers_of_g = g_table.batch_mul(&powers_of_beta);

        let h_table = BatchMulPreprocessing::new(h, max_degree);
        let powers_of_h = h_table.batch_mul(&powers_of_beta);

        let pp = UniversalParams {
            powers_of_g,
            powers_of_h,
        };

        //end_timer!(setup_time);
        Ok(pp)
    }

    pub fn commit_g1(params: &UniversalParams<E>, polynomial: &P) -> Result<E::G1Affine, Error> {
        let d = polynomial.degree();
        check_degree_is_too_large(d, params.powers_of_g.len())?;

        //let msm_time = start_timer!(|| "MSM to compute commitment to plaintext poly");
        let commitment =
            <E::G1 as VariableBaseMSM>::msm(&params.powers_of_g[..=d], &polynomial.coeffs()[..=d])
                .expect("precondition: bases and scalars length match");
        //end_timer!(msm_time);
        Ok(commitment.into_affine())
    }

    pub fn commit_g2(params: &UniversalParams<E>, polynomial: &P) -> Result<E::G2Affine, Error> {
        let d = polynomial.degree();
        check_degree_is_too_large(d, params.powers_of_h.len())?;

        //let msm_time = start_timer!(|| "MSM to compute commitment to plaintext poly");
        let commitment =
            <E::G2 as VariableBaseMSM>::msm(&params.powers_of_h[..=d], &polynomial.coeffs()[..=d])
                .expect("precondition: bases and scalars length match");
        //end_timer!(msm_time);

        Ok(commitment.into_affine())
    }

    pub fn compute_opening_proof(
        params: &UniversalParams<E>,
        polynomial: &P,
        point: &E::ScalarField,
    ) -> Result<E::G1Affine, Error> {
        let eval = polynomial.evaluate(point);
        let eval_as_poly = P::from_coefficients_vec(vec![eval]);
        let numerator = polynomial.clone().sub(&eval_as_poly);
        let divisor =
            P::from_coefficients_vec(vec![E::ScalarField::zero() - point, E::ScalarField::one()]);
        let witness_polynomial = numerator.div(&divisor);

        Self::commit_g1(params, &witness_polynomial)
    }
}

fn check_degree_is_too_large(degree: usize, num_powers: usize) -> Result<(), Error> {
    let num_coefficients = degree + 1;
    if num_coefficients > num_powers {
        Err(Error::TooManyCoefficients {
            num_coefficients,
            num_powers,
        })
    } else {
        Ok(())
    }
}
