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

use crate::utils;
use ark_poly_commit::{
    kzg10::{self, *},
    PCCommitmentState,
};

pub type KZG = KZG10<Bls12_381, UniPoly381>;
pub type UniPoly381 = DensePolynomial<<Bls12_381 as Pairing>::ScalarField>;
pub type F = ark_bls12_381::Fr;
pub type G1 = <Bls12_381 as Pairing>::G1Affine;
pub type G2 = <Bls12_381 as Pairing>::G2Affine;

#[derive(Clone)]
pub struct G1Com {
    pub com: CommitmentG1<Bls12_381>,
    pub randomness: Randomness<F, UniPoly381>,
}

impl G1Com {
    fn map(&self, f: impl Fn(G1) -> G1) -> Self {
        G1Com {
            com: self.com.map(f),
            randomness: self.randomness.clone(),
        }
    }
}

#[derive(Clone)]
pub struct G2Com {
    pub com: CommitmentG2<Bls12_381>,
    pub randomness: Randomness<F, UniPoly381>,
}

impl From<(CommitmentG1<Bls12_381>, Randomness<F, UniPoly381>)> for G1Com {
    fn from(value: (CommitmentG1<Bls12_381>, Randomness<F, UniPoly381>)) -> Self {
        G1Com {
            com: value.0,
            randomness: value.1,
        }
    }
}

impl From<(CommitmentG2<Bls12_381>, Randomness<F, UniPoly381>)> for G2Com {
    fn from(value: (CommitmentG2<Bls12_381>, Randomness<F, UniPoly381>)) -> Self {
        G2Com {
            com: value.0,
            randomness: value.1,
        }
    }
}

pub type KZGProof = kzg10::Proof<Bls12_381>;

pub struct Proof {
    agg_pk: G1,
    agg_weight: F,

    r: F,

    merged_proof: KZGProof,

    psw_of_r: F,

    psw_of_r_div_ω: F,
    psw_of_r_div_ω_proof: KZGProof,
    w_of_r: F,
    b_of_r: F,
    psw_wff_q_of_r: F,
    psw_check_q_of_r: F,
    b_wff_q_of_r: F,
    b_check_q_of_r: F,

    psw_of_x_com: G1Com,
    b_of_x_com: G1Com,
    psw_wff_q_of_x_com: G1Com,
    psw_check_q_of_x_com: G1Com,
    b_wff_q_of_x_com: G1Com,
    b_check_q_of_x_com: G1Com,

    sk_q1_com: G1Com,
    sk_q2_com: G1Com,
}

struct ProverPreprocessing {
    n: usize,            //size of the committee as a power of 2
    pks: Vec<G1>,        //g^sk_i for each party i
    q1_coms: Vec<G1Com>, //preprocessed contributions for pssk_q1
    q2_coms: Vec<G1Com>, //preprocessed contributions for pssk_q2
}

struct VerifierPreprocessing {
    n: usize, //size of the committee as a power of 2
    g_0: G1,  //first element from the KZG SRS over G1
    h_0: G2,  //first element from the KZG SRS over G2
    h_1: G2,  //2nd element from the KZG SRS over G2
    l_n_minus_1_of_x_com: G1Com,
    w_of_x_com: G1Com,
    sk_of_x_com: G2Com, //commitment to the sigma_{i \in [N]} sk_i l_i(x) polynomial
    vanishing_com: G2Com, //commitment to Z(x) = x^n - 1
    x_monomial_com: G2Com, //commentment to f(x) = x
    vk: kzg10::VerifierKey<Bls12_381>,
}

struct Cache {
    lagrange_polynomials: Vec<DensePolynomial<F>>,
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
    let mut lagrange_polynomials = vec![];
    for i in 0..n {
        let l_i_of_x = utils::lagrange_poly(n, i);
        lagrange_polynomials.push(l_i_of_x);
    }
    Cache {
        lagrange_polynomials,
    }
}

pub fn main() {
    let n = 64;
    println!("n = {}", n);

    //contains commonly used objects such as lagrange polynomials
    let cache = prepare_cache(n);

    // -------------- sample one-time SRS ---------------
    //run KZG setup
    let rng = &mut test_rng();
    let params = KZG::setup(n, true, rng).expect("Setup failed");

    // -------------- sample universe specific values ---------------
    //sample random keys
    let sk: Vec<F> = sample_secret_keys(n - 1);
    //sample random weights for each party
    let weights = sample_weights(n - 1);

    // -------------- perform universe setup ---------------
    //run universe setup
    let (vp, pp) = setup(n, &params, &weights, &sk);

    // -------------- sample proof specific values ---------------
    //samples n-1 random bits
    let bitmap = sample_bitmap(n - 1, 0.9);

    let start = Instant::now();
    let π = prove(&params, &pp, &cache, &weights, &bitmap);
    let duration = start.elapsed();
    println!("Time elapsed in prover is: {:?}", duration);

    let start = Instant::now();
    verify(&vp, &π);
    let duration = start.elapsed();
    println!("Time elapsed in verifier is: {:?}", duration);
}

fn setup(
    n: usize,
    params: &UniversalParams<Bls12_381>,
    weights: &Vec<F>,
    sk: &Vec<F>,
) -> (VerifierPreprocessing, ProverPreprocessing) {
    let mut weights = weights.clone();
    let mut sk = sk.clone();

    //last element must be 0
    sk.push(F::from(0));
    weights.push(F::from(0));

    let w_of_x = compute_poly(&weights);

    let powers = &params.powers();

    let w_of_x_com = KZG::commit_g1(&powers, &w_of_x, None, None).unwrap();

    //allocate space to collect setup material from all n-1 parties
    let mut q1_contributions: Vec<Vec<G1Com>> = vec![];
    let mut q2_contributions: Vec<G1Com> = vec![];
    let mut pks: Vec<G1> = vec![];
    let mut com_sks: Vec<G2Com> = vec![];

    //collect the setup phase material from all parties
    let all_parties_setup = crossbeam::scope(|s| {
        let mut threads = Vec::new();
        for i in 0..n {
            let idx = i.clone();
            let n = n.clone();
            let sk = sk[idx];
            let thread_i = s.spawn(move |_| party_i_setup_material(&params, powers, n, idx, &sk));
            threads.push(thread_i);
        }

        threads
            .into_iter()
            .map(|t| t.join().unwrap())
            .collect::<Vec<_>>()
    })
    .unwrap();

    for (pk_i, com_sk_l_i, q1_i, q2_i) in all_parties_setup {
        q1_contributions.push(q1_i.into());
        q2_contributions.push(q2_i.into());
        pks.push(pk_i.com.0);
        com_sks.push(com_sk_l_i);
    }

    let z_of_x = utils::compute_vanishing_poly(n);
    let x_monomial = utils::compute_x_monomial();
    let l_n_minus_1_of_x = utils::lagrange_poly(n, n - 1);

    let vp = VerifierPreprocessing {
        n: n,
        g_0: params.powers_of_g[0].clone(),
        h_0: params.powers_of_h[0].clone(),
        h_1: params.powers_of_h[1].clone(),
        l_n_minus_1_of_x_com: KZG::commit_g1(&powers, &l_n_minus_1_of_x, None, None)
            .unwrap()
            .into(),
        w_of_x_com: w_of_x_com.into(),
        // combine all sk_i l_i_of_x commitments to get commitment to sk(x)
        sk_of_x_com: add_all_g2(&powers, &com_sks),
        vanishing_com: KZG::commit_g2(&powers, &z_of_x, None, None).unwrap().into(),
        x_monomial_com: KZG::commit_g2(&powers, &x_monomial, None, None)
            .unwrap()
            .into(),
        vk: params.vk(),
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
    // compute the nth root of unity
    let n = pp.n;
    let powers = params.powers();

    //adjust the weights and bitmap polynomials
    let mut weights = weights.clone();
    //compute sum of weights of active signers
    let total_active_weight = bitmap
        .iter()
        .zip(weights.iter())
        .fold(F::from(0), |acc, (&x, &y)| acc + (x * y));
    //weight's last element must the additive inverse of active weight
    weights.push(F::from(0) - total_active_weight);

    let mut bitmap = bitmap.clone();
    //bitmap's last element must be 1 for our scheme
    bitmap.push(F::from(1));

    let mut rng = test_rng();
    let r = F::rand(&mut rng);

    //compute all the scalars we will need in the prover
    let domain = Radix2EvaluationDomain::<F>::new(n as usize).unwrap();
    let ω: F = domain.group_gen;
    let r_div_ω: F = r / ω;
    let ω_inv: F = F::from(1) / ω;

    //compute all the polynomials we will need in the prover
    let z_of_x = utils::compute_vanishing_poly(n); //returns Z(X) = X^n - 1
    let l_n_minus_1_of_x = utils::lagrange_poly(n, n - 1);
    let w_of_x = compute_poly(&weights);
    let b_of_x = compute_poly(&bitmap);
    let psw_of_x = compute_psw_poly(&weights, &bitmap);
    let psw_of_x_div_ω = utils::poly_domain_mult_ω(&psw_of_x, &ω_inv);

    //ParSumW(X) = ParSumW(X/ω) + W(X) · b(X) + Z(X) · Q1(X)
    let t_of_x = &psw_of_x - psw_of_x_div_ω - (&w_of_x * &b_of_x);
    let psw_wff_q_of_x = t_of_x.div(&z_of_x);

    //L_{n−1}(X) · ParSumW(X) = Z(X) · Q2(X)
    let t_of_x = &l_n_minus_1_of_x * &psw_of_x;
    let psw_check_q_of_x = t_of_x.div(&z_of_x);

    //b(X) · b(X) − b(X) = Z(X) · Q3(X)
    let t_of_x = (&b_of_x * &b_of_x) - (&b_of_x);
    let b_wff_q_of_x = t_of_x.div(&z_of_x);

    //L_{n−1}(X) · (b(X) - 1) = Z(X) · Q4(X)
    let t_of_x = l_n_minus_1_of_x.clone().mul(
        &b_of_x
            .clone()
            .sub(&utils::compute_constant_poly(&F::from(1))),
    );
    let b_check_q_of_x = t_of_x.div(&z_of_x);

    let sk_q1_com = filter_and_add(&powers, &pp.q1_coms, &bitmap);
    let sk_q2_com = filter_and_add(&powers, &pp.q2_coms, &bitmap);
    let agg_pk = compute_apk(&pp, &bitmap, &cache);

    let psw_of_r_proof = KZG::open(&powers, &psw_of_x, r, &Randomness::empty()).unwrap();
    let w_of_r_proof = KZG::open(&powers, &w_of_x, r, &Randomness::empty()).unwrap();
    let b_of_r_proof = KZG::open(&powers, &b_of_x, r, &Randomness::empty()).unwrap();
    let psw_wff_q_of_r_proof =
        KZG::open(&powers, &psw_wff_q_of_x, r, &Randomness::empty()).unwrap();
    let psw_check_q_of_r_proof =
        KZG::open(&powers, &psw_check_q_of_x, r, &Randomness::empty()).unwrap();
    let b_wff_q_of_r_proof = KZG::open(&powers, &b_wff_q_of_x, r, &Randomness::empty()).unwrap();
    let b_check_q_of_r_proof =
        KZG::open(&powers, &b_check_q_of_x, r, &Randomness::empty()).unwrap();

    let merged_proof = kzg10::Proof::combine(
        [
            &psw_of_r_proof,
            &w_of_r_proof,
            &b_of_r_proof,
            &psw_wff_q_of_r_proof,
            &psw_check_q_of_r_proof,
            &b_wff_q_of_r_proof,
            &b_check_q_of_r_proof,
        ],
        r,
    );

    Proof {
        agg_pk: agg_pk.clone(),
        agg_weight: total_active_weight,

        r,

        psw_of_r_div_ω: psw_of_x.evaluate(&r_div_ω),
        psw_of_r_div_ω_proof: KZG::open(&powers, &psw_of_x, r_div_ω, &Randomness::empty())
            .unwrap(),

        psw_of_r: psw_of_x.evaluate(&r),
        w_of_r: w_of_x.evaluate(&r),
        b_of_r: b_of_x.evaluate(&r),
        psw_wff_q_of_r: psw_wff_q_of_x.evaluate(&r),
        psw_check_q_of_r: psw_check_q_of_x.evaluate(&r),
        b_wff_q_of_r: b_wff_q_of_x.evaluate(&r),
        b_check_q_of_r: b_check_q_of_x.evaluate(&r),

        merged_proof: merged_proof,

        psw_of_x_com: KZG::commit_g1(&powers, &psw_of_x, None, None)
            .unwrap()
            .into(),
        b_of_x_com: KZG::commit_g1(&powers, &b_of_x, None, None).unwrap().into(),
        psw_wff_q_of_x_com: KZG::commit_g1(&powers, &psw_wff_q_of_x, None, None)
            .unwrap()
            .into(),
        psw_check_q_of_x_com: KZG::commit_g1(&powers, &psw_check_q_of_x, None, None)
            .unwrap()
            .into(),
        b_wff_q_of_x_com: KZG::commit_g1(&powers, &b_wff_q_of_x, None, None)
            .unwrap()
            .into(),
        b_check_q_of_x_com: KZG::commit_g1(&powers, &b_check_q_of_x, None, None)
            .unwrap()
            .into(),

        sk_q1_com: sk_q1_com,
        sk_q2_com: sk_q2_com,
    }
}

fn verify_opening(
    vp: &VerifierPreprocessing,
    commitment: &G1Com,
    point: &F,
    evaluation: &F,
    opening_proof: &G1,
) {
    let eval_com: G1 = vp.g_0.clone().mul(evaluation).into();
    let point_com: G2 = vp.h_0.clone().mul(point).into();

    let lhs = <Bls12_381 as Pairing>::pairing(commitment.com.0 - eval_com, vp.h_0);
    let rhs = <Bls12_381 as Pairing>::pairing(opening_proof.clone(), vp.h_1 - point_com);
    assert_eq!(lhs, rhs);
}

fn verify_openings(vp: &VerifierPreprocessing, π: &Proof) {
    //adjust the w_of_x_com
    let adjustment = F::from(0) - π.agg_weight;
    let adjustment_com = vp
        .l_n_minus_1_of_x_com
        .map(|x| (x * adjustment).into_affine());
    let w_of_x_com: G1Com = vp
        .w_of_x_com
        .map(|x| x.add(adjustment_com.com.0).into_affine());

    let psw_of_r_argument = π
        .psw_of_x_com
        .map(|x| x.sub(vp.g_0 * π.psw_of_r).into_affine());
    let w_of_r_argument = w_of_x_com.map(|x| x.sub(vp.g_0 * π.w_of_r).into_affine());
    let b_of_r_argument = π.b_of_x_com.map(|x| x.sub(vp.g_0 * π.b_of_r).into_affine());
    let psw_wff_q_of_r_argument = π
        .psw_wff_q_of_x_com
        .map(|x| x.sub(vp.g_0 * π.psw_wff_q_of_r).into_affine());
    let psw_check_q_of_r_argument = π
        .psw_check_q_of_x_com
        .map(|x| x.sub(vp.g_0 * π.psw_check_q_of_r).into_affine());
    let b_wff_q_of_r_argument = π
        .b_wff_q_of_x_com
        .map(|x| x.sub(vp.g_0 * π.b_wff_q_of_r).into_affine());
    let b_check_q_of_r_argument = π
        .b_check_q_of_x_com
        .map(|x| x.sub(vp.g_0 * π.b_check_q_of_r).into_affine());

    let merged_argument = CommitmentG1::combine(
        [
            &psw_of_r_argument.com,
            &w_of_r_argument.com,
            &b_of_r_argument.com,
            &psw_wff_q_of_r_argument.com,
            &psw_check_q_of_r_argument.com,
            &b_wff_q_of_r_argument.com,
            &b_check_q_of_r_argument.com,
        ],
        π.r,
    );

    let lhs = <Bls12_381 as Pairing>::pairing(merged_argument.0, vp.h_0);
    let rhs = <Bls12_381 as Pairing>::pairing(π.merged_proof.w, vp.h_1 - vp.h_0 * π.r);
    assert_eq!(lhs, rhs);

    let domain = Radix2EvaluationDomain::<F>::new(vp.n as usize).unwrap();
    let ω: F = domain.group_gen;
    let r_div_ω: F = π.r / ω;
    verify_opening(
        vp,
        &π.psw_of_x_com,
        &r_div_ω,
        &π.psw_of_r_div_ω,
        &π.psw_of_r_div_ω_proof.w,
    );
}

fn verify(vp: &VerifierPreprocessing, π: &Proof) {
    let domain = Radix2EvaluationDomain::<F>::new(vp.n as usize).unwrap();
    let ω: F = domain.group_gen;

    verify_openings(vp, π);

    let n: u64 = vp.n as u64;
    let vanishing_of_r: F = π.r.pow([n]) - F::from(1);

    // compute L_i(r) using the relation L_i(x) = Z_V(x) / ( Z_V'(x) (x - ω^i) )
    // where Z_V'(x)^-1 = x / N for N = |V|.
    let ω_pow_n_minus_1 = ω.pow([n - 1]);
    let l_n_minus_1_of_r =
        (ω_pow_n_minus_1 / F::from(n)) * (vanishing_of_r / (π.r - ω_pow_n_minus_1));

    //assert polynomial identity for the secret part
    let lhs = <Bls12_381 as Pairing>::pairing(&π.b_of_x_com.com.0, &vp.sk_of_x_com.com.0);
    let x1 = <Bls12_381 as Pairing>::pairing(&π.sk_q1_com.com.0, &vp.vanishing_com.com.0);
    let x2 = <Bls12_381 as Pairing>::pairing(&π.sk_q2_com.com.0, &vp.x_monomial_com.com.0);
    let x3 = <Bls12_381 as Pairing>::pairing(&π.agg_pk, &vp.h_0);
    let rhs = x1 + x2 + x3;
    assert_eq!(lhs, rhs);

    //assert checks on the public part

    //ParSumW(r) − ParSumW(r/ω) − W(r) · b(r) = Q(r) · (r^n − 1)
    let lhs = π.psw_of_r - π.psw_of_r_div_ω - π.w_of_r * π.b_of_r;
    let rhs = π.psw_wff_q_of_r * vanishing_of_r;
    assert_eq!(lhs, rhs);

    //Ln−1(X) · ParSumW(X) = Z(X) · Q2(X)
    //TODO: compute l_n_minus_1_of_r in verifier -- dont put it in the proof.
    let lhs = l_n_minus_1_of_r * π.psw_of_r;
    let rhs = vanishing_of_r * π.psw_check_q_of_r;
    assert_eq!(lhs, rhs);

    //b(r) * b(r) - b(r) = Q(r) · (r^n − 1)
    let lhs = π.b_of_r * π.b_of_r - π.b_of_r;
    let rhs = π.b_wff_q_of_r * vanishing_of_r;
    assert_eq!(lhs, rhs);

    //Ln−1(X) · (b(X) − 1) = Z(X) · Q4(X)
    let lhs = l_n_minus_1_of_r * (π.b_of_r - F::from(1));
    let rhs = vanishing_of_r * π.b_check_q_of_r;
    assert_eq!(lhs, rhs);
}

fn compute_apk(pp: &ProverPreprocessing, bitmap: &Vec<F>, cache: &Cache) -> G1 {
    let n = bitmap.len();
    let mut exponents = vec![];
    for i in 0..n {
        //let l_i_of_x = utils::lagrange_poly(n, i);
        let l_i_of_x = &cache.lagrange_polynomials[i];
        let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
        let active = bitmap[i] == F::from(1);
        exponents.push(if active { l_i_of_0 } else { F::from(0) });
    }

    <<Bls12_381 as Pairing>::G1 as VariableBaseMSM>::msm(&pp.pks[..], &exponents)
        .unwrap()
        .into_affine()
}

fn preprocess_q1_contributions(q1_contributions: &Vec<Vec<G1Com>>) -> Vec<G1Com> {
    // TODOO: deal with the randomness...
    let n = q1_contributions.len();
    let mut q1_coms = vec![];

    for i in 0..n {
        let mut party_i_q1_com = q1_contributions[i][i].clone();
        for j in 0..n {
            if i != j {
                let party_j_contribution = q1_contributions[j][i].clone();
                party_i_q1_com.com += (F::ONE, &party_j_contribution.com);
            }
        }
        q1_coms.push(party_i_q1_com);
    }
    q1_coms
}

fn filter_and_add(
    powers: &kzg10::Powers<Bls12_381>,
    elements: &Vec<G1Com>,
    bitmap: &Vec<F>,
) -> G1Com {
    let mut com = get_zero_poly_com_g1(&powers);
    for i in 0..bitmap.len() {
        if bitmap[i] == F::from(1) {
            com.com.add_assign((F::ONE, &elements[i].com));
        }
    }
    com
}

fn add_all_g2(powers: &kzg10::Powers<Bls12_381>, elements: &Vec<G2Com>) -> G2Com {
    let mut com = get_zero_poly_com_g2(&powers);
    for i in 0..elements.len() {
        com.com.add_assign((F::ONE, &elements[i].com));
    }
    com
}

fn get_zero_poly_com_g1(powers: &kzg10::Powers<'_, Bls12_381>) -> G1Com {
    let zero_poly = utils::compute_constant_poly(&F::from(0));
    KZG::commit_g1(&powers, &zero_poly, None, None)
        .unwrap()
        .into()
}

fn get_zero_poly_com_g2(powers: &kzg10::Powers<'_, Bls12_381>) -> G2Com {
    let zero_poly = utils::compute_constant_poly(&F::from(0));
    KZG::commit_g2(&powers, &zero_poly, None, None)
        .unwrap()
        .into()
}

pub(crate) fn sample_secret_keys(num_parties: usize) -> Vec<F> {
    let mut rng = test_rng();
    let mut keys = vec![];
    for _ in 0..num_parties {
        keys.push(F::rand(&mut rng));
    }
    keys
}

pub(crate) fn compute_poly(v: &Vec<F>) -> DensePolynomial<F> {
    let n = v.len();
    let mut evals = vec![];
    for i in 0..n {
        evals.push(v[i]);
    }

    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let eval_form = Evaluations::from_vec_and_domain(evals, domain);
    eval_form.interpolate()
}

pub(crate) fn compute_psw_poly(weights: &Vec<F>, bitmap: &Vec<F>) -> DensePolynomial<F> {
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
    powers: &kzg10::Powers<Bls12_381>,
    n: usize,
    i: usize,
    sk_i: &F,
) -> (G1Com, G2Com, Vec<G1Com>, G1Com) {
    //let us compute the q1 term
    let l_i_of_x = utils::lagrange_poly(n, i);
    let z_of_x = utils::compute_vanishing_poly(n);

    let mut q1_material = vec![];
    //let us compute the cross terms of q1
    for j in 0..n {
        let num: DensePolynomial<F>; // = compute_constant_poly(&F::from(0));
        if i == j {
            num = &(&l_i_of_x * &l_i_of_x) - &l_i_of_x;
        } else {
            //cross-terms
            let l_j_of_x = utils::lagrange_poly(n, j);
            num = &l_j_of_x * &l_i_of_x;
        }
        let f = num.div(&z_of_x);
        let sk_times_f = utils::poly_eval_mult_c(&f, &sk_i);

        let com = KZG::commit_g1(&powers, &sk_times_f, None, None).unwrap();

        q1_material.push(com.into());
    }

    let x_monomial = utils::compute_x_monomial();
    let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
    let l_i_of_0_poly = utils::compute_constant_poly(&l_i_of_0);
    let num = &l_i_of_x - &l_i_of_0_poly;
    let den = x_monomial;
    let f = num.div(&den);
    let sk_times_f = utils::poly_eval_mult_c(&f, &sk_i);
    let q2_com = KZG::commit_g1(&powers, &sk_times_f, None, None).unwrap();

    //release my public key
    let sk_as_poly = utils::compute_constant_poly(&sk_i);
    let pk = KZG::commit_g1(&powers, &sk_as_poly, None, None).unwrap();

    let sk_times_l_i_of_x = utils::poly_eval_mult_c(&l_i_of_x, &sk_i);
    let com_sk_l_i = KZG::commit_g2(&powers, &sk_times_l_i_of_x, None, None).unwrap();

    (pk.into(), com_sk_l_i.into(), q1_material, q2_com.into())
}
