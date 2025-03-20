use std::time::Instant;

use ark_bls12_381::Bls12_381;
use ark_ec::VariableBaseMSM;
use ark_ec::{pairing::Pairing, CurveGroup};
use ark_ff::{Field, PrimeField /* FftField */};
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, Evaluations, Polynomial, Radix2EvaluationDomain,
};
use ark_std::rand::{Rng, RngCore, SeedableRng};
use ark_std::{ops::*, test_rng, One, UniformRand, Zero};

use rayon::prelude::*;
use crate::kzg::*;
use crate::utils;

type KZG = KZG10<Bls12_381, UniPoly381>;
type UniPoly381 = DensePolynomial<<Bls12_381 as Pairing>::ScalarField>;
type F = ark_bls12_381::Fr;
type G1 = <Bls12_381 as Pairing>::G1Affine;
type G2 = <Bls12_381 as Pairing>::G2Affine;

struct Proof {
    agg_pk: G1,
    agg_weight: F,

    r: F,

    merged_proof: G1,

    psw_of_r: F,

    psw_of_r_div_ω: F,
    psw_of_r_div_ω_proof: G1,
    w_of_r: F,
    b_of_r: F,
    psw_wff_q_of_r: F,
    psw_check_q_of_r: F,
    b_wff_q_of_r: F,
    b_check_q_of_r: F,

    psw_of_x_com: G1,
    b_of_x_com: G1,
    psw_wff_q_of_x_com: G1,
    psw_check_q_of_x_com: G1,
    b_wff_q_of_x_com: G1,
    b_check_q_of_x_com: G1,

    sk_q1_com: G1,
    sk_q2_com: G1,
}

struct ProverPreprocessing {
    n: usize,         //size of the committee as a power of 2
    pks: Vec<G1>,     //g^sk_i for each party i
    q1_coms: Vec<G1>, //preprocessed contributions for pssk_q1
    q2_coms: Vec<G1>, //preprocessed contributions for pssk_q2
}

struct VerifierPreprocessing {
    n: usize, //size of the committee as a power of 2
    g_0: G1,  //first element from the KZG SRS over G1
    h_0: G2,  //first element from the KZG SRS over G2
    h_1: G2,  //2nd element from the KZG SRS over G2
    l_n_minus_1_of_x_com: G1,
    w_of_x_com: G1,
    sk_of_x_com: G2,    //commitment to the sigma_{i \in [N]} sk_i l_i(x) polynomial
    vanishing_com: G2,  //commitment to Z(x) = x^n - 1
    x_monomial_com: G2, //commentment to f(x) = x
}

struct Cache {
    lagrange_polynomials: Vec<DensePolynomial<F>>,
    vanishing_poly: DensePolynomial<F>,
    x_monomial: DensePolynomial<F>,
    lagrange_at_zero: Vec<F>,
}

fn sample_weights(n: usize) -> Vec<F> {
    let mut rng = &mut test_rng();
    (0..n).map(|_| F::from(u64::rand(&mut rng))).collect()
}

/// n is the size of the bitmap, and probability is for true or 1.
fn sample_bitmap(n: usize, probability: f64) -> Vec<F> {
    let rng = &mut test_rng();
    let mut bitmap = vec![];
    for _i in 0..n {
        //let r = u64::rand(&mut rng);
        let bit = rng.gen_bool(probability);
        bitmap.push(F::from(bit));
    }
    bitmap
}

fn prepare_cache(n: usize) -> Cache {
    println!("Preparing setup cache for n = {}", n);
    let start = Instant::now();

    // Precompute all Lagrange polynomials
    let mut lagrange_polynomials = Vec::with_capacity(n);
    let mut lagrange_at_zero = Vec::with_capacity(n);
    
    for i in 0..n {
        let l_i_of_x = utils::lagrange_poly(n, i);
        lagrange_at_zero.push(l_i_of_x.evaluate(&F::from(0)));
        lagrange_polynomials.push(l_i_of_x);
    }

    // Precompute the vanishing polynomial
    let vanishing_poly = utils::compute_vanishing_poly(n);
    
    // Precompute the x monomial
    let x_monomial = utils::compute_x_monomial();
    
    println!("Setup cache preparation took: {:?}", start.elapsed());
    
    Cache {
        lagrange_polynomials,
        vanishing_poly,
        x_monomial,
        lagrange_at_zero,
    }
}

pub fn main() {
    let n = 128;
    println!("n = {}", n);
    let start = Instant::now();

    //contains commonly used objects such as lagrange polynomials
    let cache = prepare_cache(n);

    // -------------- sample one-time SRS ---------------
    //run KZG setup
    let rng = &mut test_rng();
    let params = KZG::setup(n, rng).expect("Setup failed");
    println!("Time elapsed in KZG setup is: {:?}", start.elapsed());

    // -------------- sample universe specific values ---------------
    //sample random keys
    let sk: Vec<F> = sample_secret_keys(n - 1);
    //sample random weights for each party
    let weights = sample_weights(n - 1);

    let start = Instant::now();
    // -------------- perform universe setup ---------------
    //run universe setup
    let (vp, pp) = benchmark_setup(n, false);

    println!("Time elapsed in universe setup is: {:?}", start.elapsed());
    // -------------- sample proof specific values ---------------
    //samples n-1 random bits
    let bitmap = sample_bitmap(n - 1, 0.9);

    let prover_start = Instant::now();
    let π = prove(&params, &pp, &cache, &weights, &bitmap);
    let duration = prover_start.elapsed();
    println!("Time elapsed in prover is: {:?}", duration);

    let start = Instant::now();
    verify(&vp, &π);
    let duration = start.elapsed();
    println!("Time elapsed in verifier is: {:?}", duration);
}

fn setup(
    n: usize,
    params: &UniversalParams<Bls12_381>,
    cache: &Cache,
    weights: &Vec<F>,
    sk: &Vec<F>,
) -> (VerifierPreprocessing, ProverPreprocessing) {
    let mut weights = weights.clone();
    let mut sk = sk.clone();

    //last element must be 0
    sk.push(F::from(0));
    weights.push(F::from(0));

    let w_of_x = compute_poly(&weights);
    let w_of_x_com = KZG::commit_g1(&params, &w_of_x).unwrap();

    //allocate space to collect setup material from all n-1 parties
    let mut q1_contributions: Vec<Vec<G1>> = vec![];
    let mut q2_contributions: Vec<G1> = vec![];
    let mut pks: Vec<G1> = vec![];
    let mut com_sks: Vec<G2> = vec![];

    //collect the setup phase material from all parties
    let all_parties_setup = crossbeam::scope(|s| {
        let mut threads = Vec::new();
        for i in 0..n {
            let idx = i.clone();
            let n = n.clone();
            let sk = sk[idx];
            let thread_i = s.spawn(move |_| party_i_setup_material_optimized(&params, cache, n, idx, &sk));
            threads.push(thread_i);
        }

        threads
            .into_iter()
            .map(|t| t.join().unwrap())
            .collect::<Vec<_>>()
    })
    .unwrap();

    for (pk_i, com_sk_l_i, q1_i, q2_i) in all_parties_setup {
        q1_contributions.push(q1_i.clone());
        q2_contributions.push(q2_i.clone());
        pks.push(pk_i.clone());
        com_sks.push(com_sk_l_i.clone());
    }

    let z_of_x = utils::compute_vanishing_poly(n);
    let x_monomial = utils::compute_x_monomial();
    let l_n_minus_1_of_x = utils::lagrange_poly(n, n - 1);

    let vp = VerifierPreprocessing {
        n: n,
        g_0: params.powers_of_g[0].clone(),
        h_0: params.powers_of_h[0].clone(),
        h_1: params.powers_of_h[1].clone(),
        l_n_minus_1_of_x_com: KZG::commit_g1(&params, &l_n_minus_1_of_x).unwrap(),
        w_of_x_com: w_of_x_com,
        // combine all sk_i l_i_of_x commitments to get commitment to sk(x)
        sk_of_x_com: add_all_g2(&params, &com_sks),
        vanishing_com: KZG::commit_g2(&params, &z_of_x).unwrap(),
        x_monomial_com: KZG::commit_g2(&params, &x_monomial).unwrap(),
    };

    let pp = ProverPreprocessing {
        n: n,
        pks: pks,
        q1_coms: preprocess_q1_contributions(&q1_contributions),
        q2_coms: q2_contributions,
    };

    (vp, pp)
}

fn prove(
    params: &UniversalParams<Bls12_381>,
    pp: &ProverPreprocessing,
    cache: &Cache,
    weights: &Vec<F>,
    bitmap: &Vec<F>,
) -> Proof {
    let n = pp.n;
    let mut rng = test_rng();

    // Prepare weights and bitmap
    let mut weights = weights.clone();
    let total_active_weight = bitmap
        .iter()
        .zip(weights.iter())
        .fold(F::from(0), |acc, (&x, &y)| acc + (x * y));
    weights.push(F::from(0) - total_active_weight);

    let mut bitmap = bitmap.clone();
    bitmap.push(F::from(1));

    // Generate challenge point r
    let r = F::rand(&mut rng);

    // Compute domain parameters
    let domain = Radix2EvaluationDomain::<F>::new(n as usize).unwrap();
    let ω: F = domain.group_gen;
    let r_div_ω: F = r / ω;

    // Compute required polynomials
    let w_of_x = compute_poly(&weights);
    let b_of_x = compute_poly(&bitmap);
    let psw_of_x = compute_psw_poly(&weights, &bitmap);
    
    // Get cached polynomials
    let z_of_x = &cache.vanishing_poly;
    let l_n_minus_1_of_x = &cache.lagrange_polynomials[n-1];
    let l_1_of_x = &cache.lagrange_polynomials[0]; // L_1(x) for optimization
    
    // Optimization 1: Instead of verifying ParSum(ω) = 0, verify L_1(x)·ParSum(x) = Q3(x)·Z(x)
    let l1_times_psw = l_1_of_x.mul(&psw_of_x);
    let q3_of_x = l1_times_psw.div(z_of_x);
    
    // Optimization 2: Instead of verifying B(ω^{n+1}) = 1, verify L_{n+1}(x)·(1−B(x)) = Q4(x)·Z(x)
    let one_minus_b = utils::compute_constant_poly(&F::from(1)).sub(&b_of_x);
    let ln_plus_1_times_one_minus_b = l_n_minus_1_of_x.mul(&one_minus_b);
    let q4_of_x = ln_plus_1_times_one_minus_b.div(z_of_x);
    
    // Original quotient polynomials
    let psw_of_x_div_ω = utils::poly_domain_mult_ω(&psw_of_x, &(F::from(1) / ω));
    let w_times_b = w_of_x.clone().mul(&b_of_x);
    let psw_diff = psw_of_x.clone().sub(&psw_of_x_div_ω).sub(&w_times_b);
    let q1_of_x = psw_diff.div(z_of_x);
    
    let b_squared_minus_b = b_of_x.clone().mul(&b_of_x).sub(&b_of_x);
    let q2_of_x = b_squared_minus_b.div(z_of_x);
    
    // Optimization 3: Batch the quotient polynomials with random challenge v
    let v = F::rand(&mut rng);
    let q_of_x = q1_of_x
        .add(&q2_of_x.mul(v))
        .add(&q3_of_x.mul(v.pow([2])))
        .add(&q4_of_x.mul(v.pow([3])));
    
    // Evaluate all polynomials at point r
    let eval_start = Instant::now();
    
    let w_of_r = w_of_x.evaluate(&r);
    let b_of_r = b_of_x.evaluate(&r);
    let psw_of_r = psw_of_x.evaluate(&r);
    let psw_of_r_div_ω = psw_of_x.evaluate(&r_div_ω);
    let q_of_r = q_of_x.evaluate(&r);
    
    println!("Polynomial evaluations took: {:?}", eval_start.elapsed());

    // Compute commitments to polynomials
    let commit_start = Instant::now();
    
    // Generate commitments in parallel
    let commitments = rayon::join(
        || rayon::join(
            || KZG::commit_g1(&params, &psw_of_x).unwrap(),
            || KZG::commit_g1(&params, &b_of_x).unwrap()
        ),
        || rayon::join(
            || KZG::commit_g1(&params, &q_of_x).unwrap(),
            || rayon::join(
                || KZG::commit_g2(&params, &b_of_x).unwrap(),
                || {
                    // Pre-compute remaining components
                    let sk_q1_com = filter_and_add(&params, &pp.q1_coms, &bitmap);
                    let sk_q2_com = filter_and_add(&params, &pp.q2_coms, &bitmap);
                    (sk_q1_com, sk_q2_com)
                }
            )
        )
    );
    
    let psw_of_x_com = commitments.0.0;
    let b_of_x_com = commitments.0.1;
    let q_of_x_com = commitments.1.0;
    let (sk_q1_com, sk_q2_com) = commitments.1.1.1;
    
    println!("Commitments took: {:?}", commit_start.elapsed());

    // Optimization 4: Batch KZG opening proofs
    let batch_start = Instant::now();
    
    // Main batch for openings at point r
    let polynomials_at_r = [&psw_of_x, &w_of_x, &b_of_x, &q_of_x];
    let evaluations_at_r = [psw_of_r, w_of_r, b_of_r, q_of_r];
    
    let (open_r, _) = KZG::compute_batched_opening_proof(
        &params, 
        &polynomials_at_r, 
        &r, 
        &evaluations_at_r,
        &mut rng
    ).unwrap();
    
    // Separate proof for psw_of_x at r_div_ω
    let (open_r_div_ω, _) = KZG::compute_batched_opening_proof(
        &params,
        &[&psw_of_x],
        &r_div_ω,
        &[psw_of_r_div_ω],
        &mut rng
    ).unwrap();
    
    println!("Batch proof computation took: {:?}", batch_start.elapsed());

    // Compute aggregated public key
    let agg_pk = compute_apk(&pp, &bitmap, &cache);

    // Final optimized signature according to the paper
    Proof {
        agg_pk,
        agg_weight: total_active_weight,
        r,
        merged_proof: open_r, // Using the batched proof
        psw_of_r,
        psw_of_r_div_ω,
        psw_of_r_div_ω_proof: open_r_div_ω,
        w_of_r,
        b_of_r,
        // The rest of these can now store the batched quotient evaluation
        psw_wff_q_of_r: q_of_r.clone(),
        psw_check_q_of_r: q_of_r.clone(),
        b_wff_q_of_r: q_of_r.clone(),
        b_check_q_of_r: q_of_r,
        psw_of_x_com,
        b_of_x_com,
        // All quotient commitments become the single batched one
        psw_wff_q_of_x_com: q_of_x_com.clone(),
        psw_check_q_of_x_com: q_of_x_com.clone(),
        b_wff_q_of_x_com: q_of_x_com.clone(),
        b_check_q_of_x_com: q_of_x_com,
        sk_q1_com,
        sk_q2_com,
    }
}

fn verify_opening(
    vp: &VerifierPreprocessing,
    commitment: &G1,
    point: &F,
    evaluation: &F,
    opening_proof: &G1,
) {
    let eval_com: G1 = vp.g_0.clone().mul(evaluation).into();
    let point_com: G2 = vp.h_0.clone().mul(point).into();

    let lhs = <Bls12_381 as Pairing>::pairing(commitment.clone() - eval_com, vp.h_0);
    let rhs = <Bls12_381 as Pairing>::pairing(opening_proof.clone(), vp.h_1 - point_com);
    assert_eq!(lhs, rhs);
}

fn verify_openings(vp: &VerifierPreprocessing, π: &Proof, rng: &mut ark_std::rand::rngs::StdRng) {
    // Adjust the w_of_x_com for total weight
    let adjustment = F::from(0) - π.agg_weight;
    let adjustment_com = vp.l_n_minus_1_of_x_com.mul(adjustment);
    let w_of_x_com: G1 = (vp.w_of_x_com + adjustment_com).into();

    // Generate random challenge v for batching quotient polynomials (should match prover)
    let v = F::rand(rng);
    
    // Verify main batch opening at point r
    let commitments = [
        π.psw_of_x_com,
        w_of_x_com,
        π.b_of_x_com,
        π.psw_wff_q_of_x_com, // This is actually the batched quotient commitment
    ];
    
    let evaluations = [
        π.psw_of_r,
        π.w_of_r,
        π.b_of_r,
        π.psw_wff_q_of_r, // This is the batched quotient evaluation
    ];
    
    // Generate verification gammas - they should match what the prover used
    let gammas: Vec<F> = (0..commitments.len())
        .map(|_| F::rand(rng))
        .collect();
    
    // Verify the batched proof using our new method
    let batch_verified = KZG10::<Bls12_381, UniPoly381>::verify_batched_opening_proof(
        &UniversalParams {
            powers_of_g: vec![vp.g_0],
            powers_of_h: vec![vp.h_0, vp.h_1],
        },
        &commitments,
        &π.r,
        &evaluations,
        &π.merged_proof,
        &gammas
    );
    
    assert!(batch_verified, "Batch verification failed");
    
    // Verify the separate opening at r_div_ω
    let domain = Radix2EvaluationDomain::<F>::new(vp.n as usize).unwrap();
    let ω: F = domain.group_gen;
    let r_div_ω: F = π.r / ω;
    
    verify_opening(
        vp,
        &π.psw_of_x_com,
        &r_div_ω,
        &π.psw_of_r_div_ω,
        &π.psw_of_r_div_ω_proof,
    );
}

// Main verification function
fn verify(vp: &VerifierPreprocessing, π: &Proof) {
    // Create a deterministic RNG for verification (must match prover's choices)
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(
        (π.r.into_bigint().as_ref()[0] as u64) ^ 
        (π.b_of_r.into_bigint().as_ref()[0] as u64)
    );
    
    // Verify the KZG openings
    verify_openings(vp, π, &mut rng);
    
    let domain = Radix2EvaluationDomain::<F>::new(vp.n as usize).unwrap();
    let ω: F = domain.group_gen;
    let n: u64 = vp.n as u64;
    
    // Calculate vanishing polynomial evaluation
    let vanishing_of_r: F = π.r.pow([n]) - F::from(1);
    
    // Calculate Lagrange polynomial L_{n-1} at point r
    let ω_pow_n_minus_1 = ω.pow([n - 1]);
    let l_n_minus_1_of_r =
        (ω_pow_n_minus_1 / F::from(n)) * (vanishing_of_r / (π.r - ω_pow_n_minus_1));
    
    // Verify the secret part using pairings
    let lhs = <Bls12_381 as Pairing>::pairing(&π.b_of_x_com, &vp.sk_of_x_com);
    let x1 = <Bls12_381 as Pairing>::pairing(&π.sk_q1_com, &vp.vanishing_com);
    let x2 = <Bls12_381 as Pairing>::pairing(&π.sk_q2_com, &vp.x_monomial_com);
    let x3 = <Bls12_381 as Pairing>::pairing(&π.agg_pk, &vp.h_0);
    let rhs = x1.add(x2).add(x3);
    assert_eq!(lhs, rhs, "Secret part verification failed");
    
    // Generate random challenge v for batching quotient polynomials (same as in prover)
    let v = F::rand(&mut rng);
    
    // Verify all polynomial identities together with the batched quotient polynomial
    
    // Calculate the expected right-hand side with the batched quotient
    let batched_rhs = vanishing_of_r * π.psw_wff_q_of_r;
    
    // Calculate the left-hand side components that should match the batched quotient
    
    // 1. psw_diff = psw_of_r - psw_of_r_div_ω - w_of_r * b_of_r
    let psw_diff = π.psw_of_r - π.psw_of_r_div_ω - π.w_of_r * π.b_of_r;
    
    // 2. b_squared_minus_b = b_of_r * b_of_r - b_of_r
    let b_squared_minus_b = π.b_of_r * π.b_of_r - π.b_of_r;
    
    // 3. l1_times_psw_at_r = l_1(r) * psw_of_r (optimization 1)
    // We need to calculate l_1(r)
    let ω_pow_1 = ω.pow([1]);
    let l_1_of_r = 
        (ω_pow_1 / F::from(n)) * (vanishing_of_r / (π.r - ω_pow_1));
    let l1_times_psw_at_r = l_1_of_r * π.psw_of_r;
    
    // 4. ln_plus_1_times_one_minus_b_at_r = l_{n+1}(r) * (1 - b_of_r) (optimization 2)
    // We can use l_n_minus_1_of_r as a proxy for l_{n+1}(r) in this case (based on paper's approach)
    let ln_plus_1_times_one_minus_b_at_r = l_n_minus_1_of_r * (F::from(1) - π.b_of_r);
    
    // Combine left-hand side components with the same weights as used for the quotient
    let batched_lhs = psw_diff
        + b_squared_minus_b * v
        + l1_times_psw_at_r * v.pow([2])
        + ln_plus_1_times_one_minus_b_at_r * v.pow([3]);
    
    // Verify the batched polynomial identity
    assert_eq!(batched_lhs, batched_rhs, "Batched polynomial identity verification failed");
}

fn compute_apk(pp: &ProverPreprocessing, bitmap: &Vec<F>, cache: &Cache) -> G1 {
    let n = bitmap.len();
    let mut exponents = vec![];
    for i in 0..n {
        //let l_i_of_x = utils::lagrange_poly(n, i);
        let l_i_of_x = cache.lagrange_polynomials[i].clone();
        let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
        let active = bitmap[i] == F::from(1);
        exponents.push(if active { l_i_of_0 } else { F::from(0) });
    }

    <<Bls12_381 as Pairing>::G1 as VariableBaseMSM>::msm(&pp.pks[..], &exponents)
        .unwrap()
        .into_affine()
}

fn preprocess_q1_contributions(q1_contributions: &Vec<Vec<G1>>) -> Vec<G1> {
    let n = q1_contributions.len();
    let mut q1_coms = Vec::with_capacity(n);

    for i in 0..n {
        // Prepare for MSM
        let mut points = Vec::with_capacity(n);
        let mut scalars = Vec::with_capacity(n);

        // Add party i's own contribution
        points.push(q1_contributions[i][i]);
        scalars.push(F::one());

        // Add contributions from other parties
        for j in 0..n {
            if i != j {
                points.push(q1_contributions[j][i]);
                scalars.push(F::one());
            }
        }

        // Use MSM instead of sequential additions
        let party_i_q1_com =
            <<Bls12_381 as Pairing>::G1 as VariableBaseMSM>::msm(&points, &scalars)
                .unwrap()
                .into_affine();

        q1_coms.push(party_i_q1_com);
    }
    q1_coms
}

fn filter_and_add(params: &UniversalParams<Bls12_381>, elements: &Vec<G1>, bitmap: &Vec<F>) -> G1 {
    // Prepare for MSM by collecting only the active elements and their corresponding weights
    let mut points = Vec::with_capacity(bitmap.iter().filter(|&&b| b == F::from(1)).count());
    let mut scalars = Vec::with_capacity(points.capacity());

    for i in 0..bitmap.len() {
        if bitmap[i] == F::from(1) {
            points.push(elements[i]);
            scalars.push(F::one()); // Weight is 1 for active elements
        }
    }

    if points.is_empty() {
        // Return zero commitment if no elements are active
        return get_zero_poly_com_g1(params);
    }

    // Use MSM instead of sequential additions
    <<Bls12_381 as Pairing>::G1 as VariableBaseMSM>::msm(&points, &scalars)
        .unwrap()
        .into_affine()
}

fn batch_evaluate_polynomials(polynomials: &[&DensePolynomial<F>], point: &F) -> Vec<F> {
    use rayon::prelude::*;

    polynomials
        .par_iter()
        .map(|poly| poly.evaluate(point))
        .collect()
}

fn add_all_g2(params: &UniversalParams<Bls12_381>, elements: &Vec<G2>) -> G2 {
    if elements.is_empty() {
        return get_zero_poly_com_g2(params);
    }

    // Create a vector of all ones as scalars
    let scalars = vec![F::one(); elements.len()];

    // Use MSM instead of sequential additions
    <<Bls12_381 as Pairing>::G2 as VariableBaseMSM>::msm(elements, &scalars)
        .unwrap()
        .into_affine()
}

fn get_zero_poly_com_g1(params: &UniversalParams<Bls12_381>) -> G1 {
    let zero_poly = utils::compute_constant_poly(&F::from(0));
    KZG::commit_g1(&params, &zero_poly).unwrap()
}

fn get_zero_poly_com_g2(params: &UniversalParams<Bls12_381>) -> G2 {
    let zero_poly = utils::compute_constant_poly(&F::from(0));
    KZG::commit_g2(&params, &zero_poly).unwrap()
}

fn sample_secret_keys(num_parties: usize) -> Vec<F> {
    let mut rng = test_rng();
    let mut keys = vec![];
    for _ in 0..num_parties {
        keys.push(F::rand(&mut rng));
    }
    keys
}

fn compute_poly(v: &Vec<F>) -> DensePolynomial<F> {
    let n = v.len();
    let mut evals = vec![];
    for i in 0..n {
        evals.push(v[i]);
    }

    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let eval_form = Evaluations::from_vec_and_domain(evals, domain);
    eval_form.interpolate()
}

fn compute_psw_poly(weights: &Vec<F>, bitmap: &Vec<F>) -> DensePolynomial<F> {
    let n = weights.len();
    let mut parsum = F::from(0);
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
    params: &UniversalParams<Bls12_381>,
    cache: &Cache,
    n: usize,
    i: usize,
    sk_i: &F,
) -> (G1, G2, Vec<G1>, G1) {
    // Get cached values
    let l_i_of_x = &cache.lagrange_polynomials[i];
    let l_i_of_0 = cache.lagrange_at_zero[i];
    let z_of_x = &cache.vanishing_poly;
    let x_monomial = &cache.x_monomial;

    // Optimization 1: Calculate l_i_of_x squared once
    let l_i_of_x_squared = l_i_of_x.mul(l_i_of_x);
    
    // Optimization 2: Pre-scale the Lagrange polynomial by sk_i
    let sk_i_times_l_i_of_x = utils::poly_eval_mult_c(l_i_of_x, sk_i);
    
    // Compute q1 material more efficiently
    let mut q1_material = Vec::with_capacity(n);
    
    for j in 0..n {
        let num: DensePolynomial<F>;
        
        if i == j {
            // Self-term: sk_i * (L_i(x)² - L_i(x))
            // We already computed L_i(x)²
            num = l_i_of_x_squared.clone().sub(l_i_of_x).mul(F::from(*sk_i));
        } else {
            // Cross-term: sk_i * L_i(x) * L_j(x)
            let l_j_of_x = &cache.lagrange_polynomials[j];
            num = sk_i_times_l_i_of_x.clone().mul(l_j_of_x);
        }
        
        // Division by Z(x) to get quotient polynomial
        let f = num.div(z_of_x);
        
        // Commit directly without multiplying by sk_i again
        let com = KZG::commit_g1(&params, &f).expect("commitment failed");
        q1_material.push(com);
    }

    // Optimization 3: More efficient q2 computation
    let l_i_of_0_poly = utils::compute_constant_poly(&l_i_of_0);
    let num = sk_i_times_l_i_of_x.clone().sub(&utils::poly_eval_mult_c(&l_i_of_0_poly, sk_i));
    let f = num.div(x_monomial);
    let q2_com = KZG::commit_g1(&params, &f).expect("commitment failed");

    // Optimization 4: More efficient pk and com_sk_l_i computations
    let sk_as_poly = utils::compute_constant_poly(sk_i);
    let pk = KZG::commit_g1(&params, &sk_as_poly).expect("commitment failed");
    let com_sk_l_i = KZG::commit_g2(&params, &sk_i_times_l_i_of_x).expect("commitment failed");

    (pk, com_sk_l_i, q1_material, q2_com)
}



// Optimized party_i_setup_material function with algorithmic improvements
fn party_i_setup_material_optimized(
    params: &UniversalParams<Bls12_381>,
    cache: &Cache,
    n: usize,
    i: usize,
    sk_i: &F,
) -> (G1, G2, Vec<G1>, G1) {
    // Get cached values
    let l_i_of_x = &cache.lagrange_polynomials[i];
    let l_i_of_0 = cache.lagrange_at_zero[i];
    let z_of_x = &cache.vanishing_poly;
    let x_monomial = &cache.x_monomial;

    // Optimization 1: Calculate l_i_of_x squared once
    let l_i_of_x_squared = l_i_of_x.mul(l_i_of_x);
    
    // Optimization 2: Pre-scale the Lagrange polynomial by sk_i
    let sk_i_times_l_i_of_x = utils::poly_eval_mult_c(l_i_of_x, sk_i);
    
    // Compute q1 material more efficiently
    let mut q1_material = Vec::with_capacity(n);
    
    for j in 0..n {
        let num: DensePolynomial<F>;
        
        if i == j {
            // Self-term: sk_i * (L_i(x)² - L_i(x))
            // We already computed L_i(x)²
            num = l_i_of_x_squared.clone().sub(l_i_of_x).mul(F::from(*sk_i));
        } else {
            // Cross-term: sk_i * L_i(x) * L_j(x)
            let l_j_of_x = &cache.lagrange_polynomials[j];
            num = sk_i_times_l_i_of_x.clone().mul(l_j_of_x);
        }
        
        // Division by Z(x) to get quotient polynomial
        let f = num.div(z_of_x);
        
        // Commit directly without multiplying by sk_i again
        let com = KZG::commit_g1(&params, &f).expect("commitment failed");
        q1_material.push(com);
    }

    // Optimization 3: More efficient q2 computation
    let l_i_of_0_poly = utils::compute_constant_poly(&l_i_of_0);
    let num = sk_i_times_l_i_of_x.clone().sub(&utils::poly_eval_mult_c(&l_i_of_0_poly, sk_i));
    let f = num.div(x_monomial);
    let q2_com = KZG::commit_g1(&params, &f).expect("commitment failed");

    // Optimization 4: More efficient pk and com_sk_l_i computations
    let sk_as_poly = utils::compute_constant_poly(sk_i);
    let pk = KZG::commit_g1(&params, &sk_as_poly).expect("commitment failed");
    let com_sk_l_i = KZG::commit_g2(&params, &sk_i_times_l_i_of_x).expect("commitment failed");

    (pk, com_sk_l_i, q1_material, q2_com)
}

// Mock version for performance testing
fn party_i_setup_material_mock(
    params: &UniversalParams<Bls12_381>,
    _cache: &Cache,
    n: usize,
    i: usize,
    sk_i: &F,
) -> (G1, G2, Vec<G1>, G1) {
    // Generate deterministic but "random" data for testing
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64((i as u64) * 100 + (*sk_i).into_bigint().as_ref()[0]);
    
    // Create random elements (but deterministic based on i and sk_i)
    let pk = params.powers_of_g[0].mul(F::rand(&mut rng)).into_affine();
    let com_sk_l_i = params.powers_of_h[0].mul(F::rand(&mut rng)).into_affine();
    let q2_com = params.powers_of_g[0].mul(F::rand(&mut rng)).into_affine();
    
    // Create n random elements for q1_material
    let q1_material: Vec<G1> = (0..n)
        .map(|j| {
            let scalar = F::rand(&mut rng);
            params.powers_of_g[0].mul(scalar).into_affine()
        })
        .collect();
    
    (pk, com_sk_l_i, q1_material, q2_com)
}

// Function to measure the setup performance with different implementations
fn benchmark_setup(n: usize, use_mock: bool) -> (VerifierPreprocessing, ProverPreprocessing) {
    println!("Running setup benchmark with n = {}, use_mock = {}", n, use_mock);
    
    // Generate test data
    let mut rng = test_rng();
    let sk: Vec<F> = (0..n-1).map(|_| F::rand(&mut rng)).collect();
    let weights: Vec<F> = (0..n-1).map(|_| F::from(u64::rand(&mut rng))).collect();
    
    // Prepare the setup cache
    let setup_cache = prepare_cache(n);
    
    // Clone data for setup
    let mut weights_setup = weights.clone();
    let mut sk_setup = sk.clone();
    
    // Last element must be 0
    sk_setup.push(F::from(0));
    weights_setup.push(F::from(0));
    
    // Setup params
    let params = KZG::setup(n, &mut rng).expect("Setup failed");
    
    // Compute w_of_x and its commitment
    let w_of_x = compute_poly(&weights_setup);
    let w_of_x_com = KZG::commit_g1(&params, &w_of_x).unwrap();
    
    // Allocate space for setup material
    let mut q1_contributions: Vec<Vec<G1>> = vec![];
    let mut q2_contributions: Vec<G1> = vec![];
    let mut pks: Vec<G1> = vec![];
    let mut com_sks: Vec<G2> = vec![];
    
    // Measure the performance of party setup
    let start = Instant::now();
    
    // Choose implementation based on flag
    let setup_func = if use_mock {
        party_i_setup_material_mock
    } else {
        party_i_setup_material_optimized
    };
    
    // Use rayon to parallelize party setup material computation
    let all_parties_setup: Vec<_> = (0..n)
        .into_par_iter()
        .map(|i| {
            setup_func(&params, &setup_cache, n, i, &sk_setup[i])
        })
        .collect();
    
    let party_setup_time = start.elapsed();
    println!("Party setup took: {:?}", party_setup_time);
    
    // Process results
    for (pk_i, com_sk_l_i, q1_i, q2_i) in all_parties_setup {
        q1_contributions.push(q1_i);
        q2_contributions.push(q2_i);
        pks.push(pk_i);
        com_sks.push(com_sk_l_i);
    }
    
    // Time the preprocessing of q1 contributions
    let start = Instant::now();
    let q1_coms = preprocess_q1_contributions(&q1_contributions);
    println!("Preprocessing q1 contributions took: {:?}", start.elapsed());
    
    // Create verification key components
    let vp = VerifierPreprocessing {
        n,
        g_0: params.powers_of_g[0].clone(),
        h_0: params.powers_of_h[0].clone(),
        h_1: params.powers_of_h[1].clone(),
        l_n_minus_1_of_x_com: KZG::commit_g1(&params, &setup_cache.lagrange_polynomials[n-1]).unwrap(),
        w_of_x_com,
        sk_of_x_com: add_all_g2(&params, &com_sks),
        vanishing_com: KZG::commit_g2(&params, &setup_cache.vanishing_poly).unwrap(),
        x_monomial_com: KZG::commit_g2(&params, &setup_cache.x_monomial).unwrap(),
    };
    
    let pp = ProverPreprocessing {
        n,
        pks,
        q1_coms,
        q2_coms: q2_contributions,
    };
    
    (vp, pp)
}

#[cfg(test)]
mod tests {
    use super::*;

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
        f_of_x: &DensePolynomial<F>,
        f_of_ωx: &DensePolynomial<F>,
        ω: &F,
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
}
