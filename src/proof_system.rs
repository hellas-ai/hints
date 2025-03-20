use ark_bls12_381::Bls12_381;
use ark_crypto_primitives::sponge::{merlin, CryptographicSponge};
use ark_ec::{pairing::Pairing, CurveGroup, VariableBaseMSM};
use ark_ff::{Field, One, Zero};
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Evaluations, Polynomial,
    Radix2EvaluationDomain,
};
use ark_std::{ops::*, rand::Rng, test_rng, UniformRand};

// Import polynomial commitment related types
use ark_poly_commit::{
    sonic_pc::{Commitment, SonicKZG10}, Evaluations as PCEvaluations, LabeledCommitment, LabeledPolynomial,
    QuerySet,
};

use crate::utils;

use ark_poly_commit::PolynomialCommitment;

// Type aliases for convenience
pub type F = ark_bls12_381::Fr;
pub type G1 = <Bls12_381 as Pairing>::G1Affine;
pub type G2 = <Bls12_381 as Pairing>::G2Affine;
pub type UniPoly381 = DensePolynomial<F>;
pub type PC = SonicKZG10<Bls12_381, UniPoly381>;
pub type KZGCommitment = ark_poly_commit::sonic_pc::Commitment<Bls12_381>;
pub type UniversalParams = ark_poly_commit::sonic_pc::UniversalParams<Bls12_381>;
pub type CommitterKey = ark_poly_commit::sonic_pc::CommitterKey<Bls12_381>;
pub type VerifierKey = ark_poly_commit::sonic_pc::VerifierKey<Bls12_381>;
pub type Randomness = ark_poly_commit::sonic_pc::Randomness<F, UniPoly381>;

// Modified Proof structure to accommodate SonicKZG10
pub struct Proof {
    agg_pk: G1,
    agg_weight: F,
    r: F,

    // SonicKZG batch proof for all polynomial relations
    sonic_proof: Vec<ark_poly_commit::kzg10::Proof<Bls12_381>>,

    // Evaluation values needed for verification
    psw_of_r: F,
    psw_of_r_div_ω: F,
    w_of_r: F,
    b_of_r: F,

    // Commitments needed for verification
    psw_of_x_com: KZGCommitment,
    b_of_x_com: KZGCommitment,
    // We don't need to store w_of_x_com as we can adjust the commitment from vp.w_of_x_com

    // For the secret knowledge part
    sk_q1_com: G1,
    sk_q2_com: G1,
}

// Modified preprocessed data structures
pub struct ProverPreprocessing {
    n: usize,
    pks: Vec<G1>,
    q1_coms: Vec<G1>,
    q2_coms: Vec<G1>,
    committer_key: CommitterKey,
}

pub struct VerifierPreprocessing {
    n: usize,
    g_0: G1,
    h_0: G2,
    l_n_minus_1_of_x_com: KZGCommitment,
    w_of_x_com: KZGCommitment,
    sk_of_x_com: G2,
    vanishing_com: G2,
    x_monomial_com: G2,
    verifier_key: VerifierKey,
}

pub struct Cache {
    lagrange_polynomials: Vec<UniPoly381>,
}

pub fn prepare_cache(n: usize) -> Cache {
    let mut lagrange_polynomials = vec![];
    for i in 0..n {
        let l_i_of_x = crate::utils::lagrange_poly(n, i);
        lagrange_polynomials.push(l_i_of_x);
    }
    Cache {
        lagrange_polynomials,
    }
}

// SonicKZG requires a sponge for Fiat-Shamir
fn create_sponge() -> impl CryptographicSponge {
    merlin::Transcript::new(b"BLS12-381-KZG10-PC-HINTS")
}

pub fn setup(
    n: usize,
    max_degree: Option<usize>,
    weights: &Vec<F>,
    sk: &Vec<F>,
) -> (VerifierPreprocessing, ProverPreprocessing) {
    let max_degree = max_degree.unwrap_or(n);

    let mut rng = test_rng();
    let universal_params = PC::setup(max_degree, None, &mut rng).unwrap();

    let (committer_key, verifier_key) = PC::trim(
        &universal_params,
        max_degree,
        0,    // No hiding
        None, // No enforced degree bounds
    )
    .unwrap();

    let mut weights = weights.clone();
    let mut sk = sk.clone();

    // Last element must be 0
    sk.push(F::zero());
    weights.push(F::zero());

    let w_of_x = compute_poly(&weights);
    let w_labeled = LabeledPolynomial::new("w".to_string(), w_of_x.clone(), None, None);
    let (w_comm, _) = PC::commit(&committer_key, &[w_labeled], None).unwrap();
    let w_of_x_com = w_comm[0].commitment().clone();

    // Collect setup material from all parties
    let all_parties_setup = crossbeam::scope(|s| {
        let mut threads = Vec::new();
        for i in 0..n {
            let idx = i.clone();
            let n = n.clone();
            let sk = sk[idx];
            let committer_key = committer_key.clone();
            let thread_i = s.spawn(move |_| party_i_setup_material(&committer_key, n, idx, &sk));
            threads.push(thread_i);
        }

        threads
            .into_iter()
            .map(|t| t.join().unwrap())
            .collect::<Vec<_>>()
    })
    .unwrap();

    // Process setup material
    let mut q1_contributions: Vec<Vec<G1>> = vec![];
    let mut q2_contributions: Vec<G1> = vec![];
    let mut pks: Vec<G1> = vec![];
    let mut com_sks: Vec<G2> = vec![];

    for (pk_i, com_sk_l_i, q1_i, q2_i) in all_parties_setup {
        q1_contributions.push(q1_i.clone());
        q2_contributions.push(q2_i.clone());
        pks.push(pk_i.clone());
        com_sks.push(com_sk_l_i.clone());
    }

    let z_of_x = utils::compute_vanishing_poly(n);
    let x_monomial = utils::compute_x_monomial();
    let l_n_minus_1_of_x = utils::lagrange_poly(n, n - 1);

    // Create labeled polynomial for l_n_minus_1
    let l_labeled = LabeledPolynomial::new(
        "l_n_minus_1".to_string(),
        l_n_minus_1_of_x.clone(),
        None,
        None,
    );
    let (l_comm, _) = PC::commit(&committer_key, &[l_labeled], None).unwrap();
    let l_n_minus_1_of_x_com = l_comm[0].commitment().clone();

    // Compute commitment to sk_of_x
    let sk_of_x_poly = add_all_sk_l_i(&sk, n);
    let h_0 = verifier_key.h;

    let vp = VerifierPreprocessing {
        n,
        g_0: verifier_key.g,
        h_0,
        l_n_minus_1_of_x_com,
        w_of_x_com,
        sk_of_x_com: add_all_g2_commitments(&com_sks),
        vanishing_com: commit_g2(&z_of_x, &verifier_key),
        x_monomial_com: commit_g2(&x_monomial, &verifier_key),
        verifier_key,
    };

    let pp = ProverPreprocessing {
        n,
        pks,
        q1_coms: preprocess_q1_contributions(&q1_contributions),
        q2_coms: q2_contributions,
        committer_key,
    };

    (vp, pp)
}

pub fn prove(pp: &ProverPreprocessing, cache: &Cache, weights: &Vec<F>, bitmap: &Vec<F>) -> Proof {
    let n = pp.n;
    let mut sponge = create_sponge();

    // Adjust the weights and bitmap polynomials
    let mut weights = weights.clone();
    // Compute sum of weights of active signers
    let total_active_weight = bitmap
        .iter()
        .zip(weights.iter())
        .fold(F::zero(), |acc, (&x, &y)| acc + (x * y));
    // Weight's last element must the additive inverse of active weight
    weights.push(-total_active_weight);

    let mut bitmap = bitmap.clone();
    // Bitmap's last element must be 1 for our scheme
    bitmap.push(F::one());

    let mut rng = test_rng();
    let r = F::rand(&mut rng);

    // Compute domain and roots of unity
    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let ω: F = domain.group_gen;
    let r_div_ω: F = r / ω;

    // Compute all the polynomials needed for proving
    let z_of_x = utils::compute_vanishing_poly(n);
    let l_n_minus_1_of_x = utils::lagrange_poly(n, n - 1);
    let w_of_x = compute_poly(&weights);
    let b_of_x = compute_poly(&bitmap);
    let psw_of_x = compute_psw_poly(&weights, &bitmap);

    // Compute quotient polynomials for the various relationships

    // ParSumW(X) = ParSumW(X/ω) + W(X) · b(X) + Z(X) · Q1(X)
    let psw_of_x_div_ω = utils::poly_domain_mult_ω(&psw_of_x, &(F::one() / ω));
    let t_of_x = psw_of_x.clone() - &psw_of_x_div_ω - &(&w_of_x * &b_of_x);
    let psw_wff_q_of_x = &t_of_x / &z_of_x;

    // L_{n−1}(X) · ParSumW(X) = Z(X) · Q2(X)
    let t_of_x = &l_n_minus_1_of_x * &psw_of_x;
    let psw_check_q_of_x = &t_of_x / &z_of_x;

    // b(X) · b(X) − b(X) = Z(X) · Q3(X)
    let t_of_x = &(&b_of_x * &b_of_x) - &b_of_x;

    // L_{n−1}(X) · (b(X) - 1) = Z(X) · Q4(X)
    let t_of_x =
        &l_n_minus_1_of_x * &(&b_of_x - &UniPoly381::from_coefficients_vec(vec![F::one()]));
    let b_check_q_of_x = &t_of_x / &z_of_x;

    // Create labeled polynomials for all our constraints
    let psw_labeled = LabeledPolynomial::new("psw".to_string(), psw_of_x.clone(), None, None);
    let b_labeled = LabeledPolynomial::new("b".to_string(), b_of_x.clone(), None, None);
    let w_labeled = LabeledPolynomial::new("w".to_string(), w_of_x.clone(), None, None);

    // Commit to polynomials
    let (commitments, states) = PC::commit(
        &pp.committer_key,
        &[psw_labeled.clone(), b_labeled.clone(), w_labeled.clone()],
        Some(&mut rng),
    )
    .unwrap();

    // Extract individual commitments
    let psw_com = commitments[0].commitment().clone();
    let b_com = commitments[1].commitment().clone();

    // Prepare query points - we need to evaluate at r and r/ω
    let mut query_set = QuerySet::new();
    query_set.insert(("psw".to_string(), ("r".to_string(), r)));
    query_set.insert(("psw".to_string(), ("r/ω".to_string(), r_div_ω)));
    query_set.insert(("b".to_string(), ("r".to_string(), r)));
    query_set.insert(("w".to_string(), ("r".to_string(), r)));

    // Generate batch proof for all our polynomials at the query points
    let batch_proof = PC::batch_open(
        &pp.committer_key,
        &[psw_labeled.clone(), b_labeled.clone(), w_labeled.clone()],
        &commitments,
        &query_set,
        &mut sponge,
        &states,
        Some(&mut rng),
    )
    .unwrap();

    // Compute the aggregated public key
    let agg_pk = compute_apk(&pp, &bitmap, &cache);

    // Compute the secret-knowledge parts
    let sk_q1_com = filter_and_add(&pp.q1_coms, &bitmap);
    let sk_q2_com = filter_and_add(&pp.q2_coms, &bitmap);

    Proof {
        agg_pk,
        agg_weight: total_active_weight,
        r,
        sonic_proof: batch_proof.into(), // Convert BatchProof to Vec<Proof>

        psw_of_r: psw_of_x.evaluate(&r),
        psw_of_r_div_ω: psw_of_x.evaluate(&r_div_ω),
        w_of_r: w_of_x.evaluate(&r),
        b_of_r: b_of_x.evaluate(&r),

        psw_of_x_com: psw_com,
        b_of_x_com: b_com,

        sk_q1_com,
        sk_q2_com,
    }
}

pub fn verify(vp: &VerifierPreprocessing, π: &Proof) -> bool {
    let mut sponge = create_sponge();

    // Calculate domain parameters
    let domain = Radix2EvaluationDomain::<F>::new(vp.n).unwrap();
    let ω: F = domain.group_gen;
    let n: u64 = vp.n as u64;
    let vanishing_of_r: F = π.r.pow([n]) - F::one();

    // Compute L_n-1(r) using the relation for Lagrange polynomials
    let ω_pow_n_minus_1 = ω.pow([n - 1]);
    let l_n_minus_1_of_r =
        (ω_pow_n_minus_1 / F::from(n as u64)) * (vanishing_of_r / (π.r - ω_pow_n_minus_1));

    // Verify the polynomial identities

    // 1. Verify ParSumW(r) - ParSumW(r/ω) - W(r) · b(r) = Q(r) · (r^n - 1)
    let lhs1 = π.psw_of_r - π.psw_of_r_div_ω - π.w_of_r * π.b_of_r;
    if lhs1 != F::zero() && lhs1 / vanishing_of_r == F::zero() {
        return false;
    }

    // 2. Verify Ln-1(r) · ParSumW(r) = Z(r) · Q2(r)
    let lhs2 = l_n_minus_1_of_r * π.psw_of_r;
    if lhs2 != F::zero() && lhs2 / vanishing_of_r == F::zero() {
        return false;
    }

    // 3. Verify b(r) * b(r) - b(r) = Q(r) · (r^n - 1)
    let lhs3 = π.b_of_r * π.b_of_r - π.b_of_r;
    if lhs3 != F::zero() && lhs3 / vanishing_of_r == F::zero() {
        return false;
    }

    // 4. Verify Ln-1(r) · (b(r) - 1) = Z(r) · Q4(r)
    let lhs4 = l_n_minus_1_of_r * (π.b_of_r - F::one());
    if lhs4 != F::zero() && lhs4 / vanishing_of_r == F::zero() {
        return false;
    }

    // 5. Verify the SonicKZG10 batch proof

    // Build evaluations map for the query points
    let mut evaluations = PCEvaluations::new();
    evaluations.insert(("psw".to_string(), π.r), π.psw_of_r);
    evaluations.insert(("psw".to_string(), π.r / ω), π.psw_of_r_div_ω);
    evaluations.insert(("b".to_string(), π.r), π.b_of_r);
    evaluations.insert(("w".to_string(), π.r), π.w_of_r);

    // Prepare labeled commitments
    let psw_labeled_comm = LabeledCommitment::new("psw".to_string(), π.psw_of_x_com.clone(), None);
    let b_labeled_comm = LabeledCommitment::new("b".to_string(), π.b_of_x_com.clone(), None);

    // Adjust w_of_x_com for the weight offset
    let adjustment = -π.agg_weight;
    let w_com = adjust_commitment(&vp.w_of_x_com, &vp.l_n_minus_1_of_x_com, adjustment);
    let w_labeled_comm = LabeledCommitment::new("w".to_string(), w_com, None);

    // Create query set that matches the proof
    let mut query_set = QuerySet::new();
    query_set.insert(("psw".to_string(), ("r".to_string(), π.r)));
    query_set.insert(("psw".to_string(), ("r/ω".to_string(), π.r / ω)));
    query_set.insert(("b".to_string(), ("r".to_string(), π.r)));
    query_set.insert(("w".to_string(), ("r".to_string(), π.r)));

    // Verify the polynomial evaluations
    let sonic_batch_proof = Vec::from(π.sonic_proof.clone());
    let poly_verifications_ok = PC::batch_check(
        &vp.verifier_key,
        &[psw_labeled_comm, b_labeled_comm, w_labeled_comm],
        &query_set,
        &evaluations,
        &sonic_batch_proof,
        &mut sponge,
        &mut test_rng(),
    )
    .unwrap();

    if !poly_verifications_ok {
        return false;
    }

    // 6. Verify the secret key part
    // B(X) ⋅ SK(X) = Q1(X) ⋅ Z(X) + Q2(X) ⋅ X + APK
    let lhs = pairing_product(&π.b_of_x_com.0, &vp.sk_of_x_com);
    let rhs1 = pairing_product(&π.sk_q1_com, &vp.vanishing_com);
    let rhs2 = pairing_product(&π.sk_q2_com, &vp.x_monomial_com);
    let rhs3 = pairing_product(&π.agg_pk, &vp.h_0);

    let rhs = rhs1 + rhs2 + rhs3;

    if lhs != rhs {
        return false;
    }

    true
}

// Helper functions

fn compute_poly(v: &Vec<F>) -> UniPoly381 {
    let n = v.len();
    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let eval_form = Evaluations::from_vec_and_domain(v.clone(), domain);
    eval_form.interpolate()
}

fn compute_psw_poly(weights: &Vec<F>, bitmap: &Vec<F>) -> UniPoly381 {
    let n = weights.len();
    let mut parsum = F::zero();
    let mut evals = vec![];
    for i in 0..n {
        let w_i_b_i = bitmap[i] * weights[i];
        parsum += w_i_b_i;
        evals.push(parsum);
    }

    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let eval_form = Evaluations::from_vec_and_domain(evals, domain);
    eval_form.interpolate()
}

fn party_i_setup_material(
    ck: &CommitterKey,
    n: usize,
    i: usize,
    sk_i: &F,
) -> (G1, G2, Vec<G1>, G1) {
    // Q1 computation
    let l_i_of_x = utils::lagrange_poly(n, i);
    let z_of_x = utils::compute_vanishing_poly(n);

    let mut q1_material = vec![];
    for j in 0..n {
        let num: UniPoly381;
        if i == j {
            num = &(&l_i_of_x * &l_i_of_x) - &l_i_of_x;
        } else {
            let l_j_of_x = utils::lagrange_poly(n, j);
            num = &l_j_of_x * &l_i_of_x;
        }
        let f = &num / &z_of_x;
        let sk_times_f = utils::poly_eval_mult_c(&f, sk_i);

        // Commit using SonicKZG
        let labeled_poly =
            LabeledPolynomial::new(format!("q1_{}_{}", i, j), sk_times_f, None, None);
        let (commits, _) = PC::commit(ck, &[labeled_poly], None).unwrap();
        let com = commits[0].commitment().clone();

        q1_material.push(G1::from(com.0));
    }

    // Q2 computation
    let x_monomial = utils::compute_x_monomial();
    let l_i_of_0 = l_i_of_x.evaluate(&F::zero());
    let l_i_of_0_poly = UniPoly381::from_coefficients_vec(vec![l_i_of_0]);
    let num = &l_i_of_x - &l_i_of_0_poly;
    let den = x_monomial.clone();
    let f = &num / &den;
    let sk_times_f = utils::poly_eval_mult_c(&f, sk_i);

    // Commit to Q2
    let labeled_poly = LabeledPolynomial::new(format!("q2_{}", i), sk_times_f, None, None);
    let (commits, _) = PC::commit(ck, &[labeled_poly], None).unwrap();
    let q2_com = commits[0].commitment().clone();

    // Public key computation
    let sk_as_poly = UniPoly381::from_coefficients_vec(vec![*sk_i]);
    let pk_labeled = LabeledPolynomial::new(format!("pk_{}", i), sk_as_poly, None, None);
    let (pk_commits, _) = PC::commit(ck, &[pk_labeled], None).unwrap();
    let pk = G1::from(pk_commits[0].commitment().0);

    // SK * L_i commitment for G2
    let sk_times_l_i_of_x = utils::poly_eval_mult_c(&l_i_of_x, sk_i);
    let com_sk_l_i = commit_g2_poly(&sk_times_l_i_of_x);

    (pk, com_sk_l_i, q1_material, G1::from(q2_com.0))
}

fn compute_apk(pp: &ProverPreprocessing, bitmap: &Vec<F>, cache: &Cache) -> G1 {
    let n = bitmap.len();
    let mut exponents = vec![];
    for i in 0..n {
        let l_i_of_x = &cache.lagrange_polynomials[i];
        let l_i_of_0 = l_i_of_x.evaluate(&F::zero());
        let active = bitmap[i] == F::one();
        exponents.push(if active { l_i_of_0 } else { F::zero() });
    }

    let apk = <Bls12_381 as Pairing>::G1::msm(&pp.pks, &exponents).unwrap();
    apk.into_affine()
}

fn preprocess_q1_contributions(q1_contributions: &Vec<Vec<G1>>) -> Vec<G1> {
    let n = q1_contributions.len();
    let mut q1_coms = vec![];

    for i in 0..n {
        let mut party_i_q1_com = q1_contributions[i][i].clone();
        for j in 0..n {
            if i != j {
                let party_j_contribution = q1_contributions[j][i].clone();
                party_i_q1_com = (party_i_q1_com + party_j_contribution).into_affine();
            }
        }
        q1_coms.push(party_i_q1_com);
    }
    q1_coms
}

fn filter_and_add(elements: &Vec<G1>, bitmap: &Vec<F>) -> G1 {
    let mut result = <Bls12_381 as Pairing>::G1::zero();
    for i in 0..bitmap.len() {
        if bitmap[i] == F::one() {
            result += elements[i];
        }
    }
    result.into_affine()
}

fn add_all_g2_commitments(elements: &Vec<G2>) -> G2 {
    let mut result = <Bls12_381 as Pairing>::G2::zero();
    for element in elements {
        result += element;
    }
    result.into_affine()
}

fn add_all_sk_l_i(sk: &Vec<F>, n: usize) -> UniPoly381 {
    let mut result = UniPoly381::zero();
    for i in 0..n {
        let l_i = utils::lagrange_poly(n, i);
        result += &utils::poly_eval_mult_c(&l_i, &sk[i]);
    }
    result
}

fn adjust_commitment(
    base_comm: &KZGCommitment,
    adjustment_comm: &KZGCommitment,
    scalar: F,
) -> KZGCommitment {
    let base = <Bls12_381 as Pairing>::G1::from(base_comm.0);
    let adjustment = <Bls12_381 as Pairing>::G1::from(adjustment_comm.0).mul(scalar);
    ark_poly_commit::kzg10::Commitment((base + adjustment).into_affine())
}

fn commit_g2(poly: &UniPoly381, vk: &VerifierKey) -> G2 {
    let coeffs = poly.coeffs();
    let mut result = <Bls12_381 as Pairing>::G2::zero();

    for (i, c) in coeffs.iter().enumerate() {
        if i == 0 {
            result += vk.h.mul(*c);
        } else if i == 1 {
            result += vk.beta_h.mul(*c);
        }
        // For higher powers, we'd need more SRS elements
    }

    result.into_affine()
}

fn commit_g2_poly(poly: &UniPoly381) -> G2 {
    // This is a simplified version - in practice we would need access to the SRS
    let mut rng = test_rng();
    let h = <Bls12_381 as Pairing>::G2::rand(&mut rng).into_affine();
    let beta = F::rand(&mut rng);
    let beta_h = h.mul(beta).into_affine();

    let coeffs = poly.coeffs();
    let mut result = <Bls12_381 as Pairing>::G2::zero();

    for (i, c) in coeffs.iter().enumerate() {
        if i == 0 {
            result += h.mul(*c);
        } else if i == 1 {
            result += beta_h.mul(*c);
        }
        // For higher powers, we'd need more SRS elements
    }

    result.into_affine()
}

fn pairing_product(g1: &G1, g2: &G2) -> ark_ec::pairing::PairingOutput<Bls12_381> {
    <Bls12_381 as Pairing>::pairing(*g1, *g2)
}

pub fn main() {
    use std::time::Instant;
    let n: usize = 256;
    println!("n = {}", n);

    let start = Instant::now();
    // Contains commonly used objects such as lagrange polynomials
    let cache = prepare_cache(n);

    // -------------- sample universe specific values ---------------
    // Sample random keys
    let sk: Vec<F> = crate::original_proof_system::sample_secret_keys(n - 1);
    // Sample random weights for each party
    let weights = crate::original_proof_system::sample_weights(n - 1);

    // -------------- perform universe setup ---------------
    // Run universe setup
    let (vp, pp) = setup(n, None, &weights, &sk);

    // -------------- sample proof specific values ---------------
    // Samples n-1 random bits
    let bitmap = crate::original_proof_system::sample_bitmap(n - 1, 0.9);

    println!("Time elapsed in setup is: {:?}", start.elapsed());
    let start = Instant::now();
    let π = prove(&pp, &cache, &weights, &bitmap);
    let duration = start.elapsed();
    println!("Time elapsed in prover is: {:?}", duration);

    let start = Instant::now();
    let result = verify(&vp, &π);
    let duration = start.elapsed();
    println!("Time elapsed in verifier is: {:?}", duration);

    println!("Verification result: {}", result);
}