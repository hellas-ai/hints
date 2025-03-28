//! SNARK for certifying weighted aggregation (implementation detail)

use ark_ec::VariableBaseMSM;
use ark_ec::{pairing::Pairing, CurveGroup};
use ark_poly::{univariate::DensePolynomial, Polynomial};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{One, Zero};

use crate::utils::{self};
use crate::{kzg::*, PublicKey};

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
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct GlobalData {
    pub params: UniversalParams<Curve>,
    pub cache: Cache,
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

        Cache {
            lagrange_polynomials,
            lagrange_coms_g1,
            lagrange_coms_g2,
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
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Cache {
    pub lagrange_polynomials: Vec<DensePolynomial<F>>,
    pub lagrange_coms_g1: Vec<G1>,
    pub lagrange_coms_g2: Vec<G2>,
}

fn compute_apk(
    all_pks: &[PublicKey],
    all_l_polys: &[DensePolynomial<F>],
    full_bitmap: &[F],
) -> G1 {
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
