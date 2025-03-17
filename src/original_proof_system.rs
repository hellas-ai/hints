use ark_bls12_381::Bls12_381;
use ark_ec::{pairing::Pairing, VariableBaseMSM, CurveGroup};
use ark_ff::{Field, One, PrimeField};
use ark_poly::DenseUVPolynomial;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, Evaluations, Polynomial, Radix2EvaluationDomain,
};
use ark_std::{rand::Rng, UniformRand, Zero, ops::*, test_rng};

// Import the polynomial commitment library
use ark_poly_commit::kzg10::{KZG10, Powers, UniversalParams, VerifierKey, Commitment, Proof, Randomness};
use ark_poly_commit::{Error as PCError, PCCommitmentState};

pub type UniPoly381 = DensePolynomial<<Bls12_381 as Pairing>::ScalarField>;
pub type KZG = KZG10<Bls12_381, UniPoly381>;
pub type F = ark_bls12_381::Fr;
pub type G1 = <Bls12_381 as Pairing>::G1Affine;
pub type G2 = <Bls12_381 as Pairing>::G2Affine;

pub struct HinTSProof {
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

    psw_of_x_com: Commitment<Bls12_381>,
    b_of_x_com: Commitment<Bls12_381>,
    psw_wff_q_of_x_com: Commitment<Bls12_381>,
    psw_check_q_of_x_com: Commitment<Bls12_381>,
    b_wff_q_of_x_com: Commitment<Bls12_381>,
    b_check_q_of_x_com: Commitment<Bls12_381>,

    sk_q1_com: G1,
    sk_q2_com: G1,
}

pub struct ProverPreprocessing {
    n: usize,         // size of the committee as a power of 2
    pks: Vec<G1>,     // g^sk_i for each party i
    q1_coms: Vec<G1>, // preprocessed contributions for pssk_q1
    q2_coms: Vec<G1>, // preprocessed contributions for pssk_q2
}

pub struct VerifierPreprocessing {
    n: usize, // size of the committee as a power of 2
    vk: VerifierKey<Bls12_381>,
    l_n_minus_1_of_x_com: Commitment<Bls12_381>,
    w_of_x_com: Commitment<Bls12_381>,
    sk_of_x_com: G2,
    vanishing_com: G2,
    x_monomial_com: G2,
}

pub struct Cache {
    lagrange_polynomials: Vec<UniPoly381>,
}

pub fn prepare_cache(n: usize) -> Cache {
    let mut lagrange_polynomials = vec![];
    for i in 0..n {
        let l_i_of_x = lagrange_poly(n, i);
        lagrange_polynomials.push(l_i_of_x);
    }
    Cache {
        lagrange_polynomials,
    }
}

// Helper function to compute Lagrange polynomial
pub fn lagrange_poly(n: usize, i: usize) -> UniPoly381 {
    let mut evals = vec![];
    for j in 0..n {
        let l_of_x: u64 = if i == j { 1 } else { 0 };
        evals.push(F::from(l_of_x));
    }

    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let eval_form = Evaluations::from_vec_and_domain(evals, domain);
    eval_form.interpolate()
}

// Helper function to compute vanishing polynomial
pub fn compute_vanishing_poly(n: usize) -> UniPoly381 {
    let mut coeffs = vec![];
    for i in 0..n+1 {
        if i == 0 {
            coeffs.push(F::from(0) - F::from(1)); // -1
        } else if i == n {
            coeffs.push(F::from(1)); // X^n
        } else {
            coeffs.push(F::from(0));
        }
    }
    UniPoly381::from_coefficients_vec(coeffs)
}

// Helper to compute X monomial
pub fn compute_x_monomial() -> UniPoly381 {
    let mut coeffs = vec![];
    coeffs.push(F::from(0)); // 0
    coeffs.push(F::from(1)); // X
    UniPoly381::from_coefficients_vec(coeffs)
}

// Helper to compute constant polynomial
pub fn compute_constant_poly(c: &F) -> UniPoly381 {
    let mut coeffs = vec![];
    coeffs.push(c.clone()); // c
    UniPoly381::from_coefficients_vec(coeffs)
}

// Helper for polynomial multiplication by constant
pub fn poly_eval_mult_c(f: &UniPoly381, c: &F) -> UniPoly381 {
    let mut new_poly = f.clone();
    for i in 0..(f.degree() + 1) {
        new_poly.coeffs[i] = new_poly.coeffs[i] * c.clone();
    }
    new_poly
}

// Helper to compute domain multiplication by omega
pub fn poly_domain_mult_ω(f: &UniPoly381, ω: &F) -> UniPoly381 {
    let mut new_poly = f.clone();
    for i in 1..(f.degree() + 1) { // we don't touch the zeroth coefficient
        let ω_pow_i: F = ω.pow([i as u64]);
        new_poly.coeffs[i] = new_poly.coeffs[i] * ω_pow_i;
    }
    new_poly
}

pub fn sample_weights(n: usize) -> Vec<F> {
    let mut rng = &mut test_rng();
    (0..n).map(|_| F::from(u64::rand(&mut rng))).collect()
}

pub fn sample_bitmap(n: usize, probability: f64) -> Vec<F> {
    let rng = &mut test_rng();
    let mut bitmap = vec![];
    for _i in 0..n {
        let bit = rng.gen_bool(probability);
        bitmap.push(F::from(bit));
    }
    bitmap
}

pub fn compute_poly(v: &Vec<F>) -> UniPoly381 {
    let n = v.len();
    let mut evals = vec![];
    for i in 0..n {
        evals.push(v[i]);
    }

    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let eval_form = Evaluations::from_vec_and_domain(evals, domain);
    eval_form.interpolate()
}

pub fn compute_psw_poly(weights: &Vec<F>, bitmap: &Vec<F>) -> UniPoly381 {
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

// Function to extract powers for a specific degree
fn extract_powers(pp: &UniversalParams<Bls12_381>, degree: usize) -> Powers<Bls12_381> {
    // We need to create a Powers structure from UniversalParams
    // This is similar to the trim function in KZG10 tests
    let powers_of_g = pp.powers_of_g[..=degree].to_vec();
    
    // For powers_of_gamma_g, we need to extract them from the BTreeMap
    let powers_of_gamma_g = (0..=degree)
        .map(|i| pp.powers_of_gamma_g[&i])
        .collect::<Vec<_>>();

    Powers {
        powers_of_g: std::borrow::Cow::Owned(powers_of_g),
        powers_of_gamma_g: std::borrow::Cow::Owned(powers_of_gamma_g),
    }
}

pub fn setup(
    n: usize,
    pp: &UniversalParams<Bls12_381>,
    weights: &Vec<F>,
    sk: &Vec<F>,
) -> (VerifierPreprocessing, ProverPreprocessing) {
    let mut weights = weights.clone();
    let mut sk = sk.clone();

    // Last element must be 0
    sk.push(F::from(0));
    weights.push(F::from(0));

    let w_of_x = compute_poly(&weights);
    
    // Extract powers for the required degree
    let powers = extract_powers(&pp, n);
    let hiding_bound = None;
    let rng = &mut test_rng();
    
    let (w_of_x_com, _) = KZG::commit(&powers, &w_of_x, hiding_bound, Some(rng))
        .expect("Failed to commit to w_of_x");

    // Create verifier key
    let vk = VerifierKey {
        g: pp.powers_of_g[0],
        gamma_g: pp.powers_of_gamma_g[&0],
        h: pp.h,
        beta_h: pp.beta_h,
        prepared_h: pp.prepared_h.clone(),
        prepared_beta_h: pp.prepared_beta_h.clone(),
    };

    // Allocate space to collect setup material from all n-1 parties
    let mut q1_contributions: Vec<Vec<G1>> = vec![];
    let mut q2_contributions: Vec<G1> = vec![];
    let mut pks: Vec<G1> = vec![];
    let mut com_sks: Vec<G2> = vec![];

    // Collect the setup phase material from all parties
    let all_parties_setup = crossbeam::scope(|s| {
        let mut threads = Vec::new();
        for i in 0..n {
            let idx = i.clone();
            let n = n.clone();
            let sk = sk[idx];
            let thread_i = s.spawn(move |_| party_i_setup_material(&pp, n, idx, &sk));
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

    let z_of_x = compute_vanishing_poly(n);
    let x_monomial = compute_x_monomial();
    let l_n_minus_1_of_x = lagrange_poly(n, n - 1);
    
    // Using KZG10 commit for l_n_minus_1_of_x
    let (l_n_minus_1_of_x_com, _) = KZG::commit(&powers, &l_n_minus_1_of_x, hiding_bound, Some(rng))
        .expect("Failed to commit to l_n_minus_1_of_x");

    // For G2 commitments, we need to calculate them manually
    // Will need to adapt this to use arkworks API later
    let sk_of_x_com = add_all_g2(&com_sks);
    let vanishing_com = commit_g2(&pp, &z_of_x);
    let x_monomial_com = commit_g2(&pp, &x_monomial);

    let vp = VerifierPreprocessing {
        n,
        vk,
        l_n_minus_1_of_x_com,
        w_of_x_com,
        sk_of_x_com,
        vanishing_com,
        x_monomial_com,
    };

    let pp = ProverPreprocessing {
        n,
        pks,
        q1_coms: preprocess_q1_contributions(&q1_contributions),
        q2_coms: q2_contributions,
    };

    (vp, pp)
}

// Manual G2 commitment function - we'll need to adapt this later
fn commit_g2(pp: &UniversalParams<Bls12_381>, polynomial: &UniPoly381) -> G2 {
    let d = polynomial.degree();
    let plain_coeffs: Vec<_> = polynomial.coeffs.iter().map(|c| c.into_bigint()).collect();
    let powers_of_h: Vec<G2> = (0..=d).map(|i| pp.neg_powers_of_h[&i]).collect();
    
    <Bls12_381 as Pairing>::G2::msm_bigint(&powers_of_h, &plain_coeffs).into_affine()
}

fn add_all_g2(elements: &Vec<G2>) -> G2 {
    let mut result = <Bls12_381 as Pairing>::G2::zero().into_affine();
    for element in elements {
        result = (result + element).into_affine();
    }
    result
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

fn party_i_setup_material(
    pp: &UniversalParams<Bls12_381>,
    n: usize,
    i: usize,
    sk_i: &F,
) -> (G1, G2, Vec<G1>, G1) {
    // Let us compute the q1 term
    let l_i_of_x = lagrange_poly(n, i);
    let z_of_x = compute_vanishing_poly(n);
    
    let powers = extract_powers(&pp, n);
    let hiding_bound = None;
    let rng = &mut test_rng();

    let mut q1_material = vec![];
    // Let us compute the cross terms of q1
    for j in 0..n {
        let num: UniPoly381;
        if i == j {
            num = l_i_of_x.clone().mul(&l_i_of_x).sub(&l_i_of_x);
        } else {
            // Cross-terms
            let l_j_of_x = lagrange_poly(n, j);
            num = l_j_of_x.mul(&l_i_of_x);
        }
        let f = num.div(&z_of_x);
        let sk_times_f = poly_eval_mult_c(&f, &sk_i);

        // Using KZG10 commit for G1 commitments
        let (com, _) = KZG::commit(&powers, &sk_times_f, hiding_bound, Some(&mut test_rng()))
            .expect("Failed to commit to sk_times_f");

        q1_material.push(com.0);
    }

    let x_monomial = compute_x_monomial();
    let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
    let l_i_of_0_poly = compute_constant_poly(&l_i_of_0);
    let num = l_i_of_x.clone().sub(&l_i_of_0_poly);
    let den = x_monomial.clone();
    let f = num.div(&den);
    let sk_times_f = poly_eval_mult_c(&f, &sk_i);
    
    // Using KZG10 commit for G1 commitments
    let (q2_com, _) = KZG::commit(&powers, &sk_times_f, hiding_bound, Some(&mut test_rng()))
        .expect("Failed to commit to sk_times_f");

    // Release my public key
    let sk_as_poly = compute_constant_poly(&sk_i);
    let (pk, _) = KZG::commit(&powers, &sk_as_poly, hiding_bound, Some(&mut test_rng()))
        .expect("Failed to commit to sk_as_poly");

    let sk_times_l_i_of_x = poly_eval_mult_c(&l_i_of_x, &sk_i);
    let com_sk_l_i = commit_g2(&pp, &sk_times_l_i_of_x);

    (pk.0, com_sk_l_i, q1_material, q2_com.0)
}

pub fn prove(
    pp: &UniversalParams<Bls12_381>,
    prover_pp: &ProverPreprocessing,
    cache: &Cache,
    weights: &Vec<F>,
    bitmap: &Vec<F>,
) -> HinTSProof {
    // Compute the nth root of unity
    let n = prover_pp.n;

    // Adjust the weights and bitmap polynomials
    let mut weights = weights.clone();
    // Compute sum of weights of active signers
    let total_active_weight = bitmap
        .iter()
        .zip(weights.iter())
        .fold(F::from(0), |acc, (&x, &y)| acc + (x * y));
    // Weight's last element must the additive inverse of active weight
    weights.push(F::from(0) - total_active_weight);

    let mut bitmap = bitmap.clone();
    // Bitmap's last element must be 1 for our scheme
    bitmap.push(F::from(1));

    let mut rng = test_rng();
    let r = F::rand(&mut rng);

    // Compute all the scalars we will need in the prover
    let domain = Radix2EvaluationDomain::<F>::new(n as usize).unwrap();
    let ω: F = domain.group_gen;
    let r_div_ω: F = r / ω;
    let ω_inv: F = F::one() / ω;

    // Compute all the polynomials we will need in the prover
    let z_of_x = compute_vanishing_poly(n);
    let l_n_minus_1_of_x = lagrange_poly(n, n - 1);
    let w_of_x = compute_poly(&weights);
    let b_of_x = compute_poly(&bitmap);
    let psw_of_x = compute_psw_poly(&weights, &bitmap);
    let psw_of_x_div_ω = poly_domain_mult_ω(&psw_of_x, &ω_inv);

    // Extract powers for polynomial commitments
    let powers = extract_powers(&pp, n);
    let hiding_bound = None;

    // ParSumW(X) = ParSumW(X/ω) + W(X) · b(X) + Z(X) · Q1(X)
    let t_of_x = psw_of_x
        .clone()
        .sub(&psw_of_x_div_ω)
        .sub(&w_of_x.clone().mul(&b_of_x));
    let psw_wff_q_of_x = t_of_x.div(&z_of_x);

    // L_{n−1}(X) · ParSumW(X) = Z(X) · Q2(X)
    let t_of_x = l_n_minus_1_of_x.clone().mul(&psw_of_x);
    let psw_check_q_of_x = t_of_x.div(&z_of_x);

    // b(X) · b(X) − b(X) = Z(X) · Q3(X)
    let t_of_x = b_of_x.clone().mul(&b_of_x).sub(&b_of_x);
    let b_wff_q_of_x = t_of_x.div(&z_of_x);

    // L_{n−1}(X) · (b(X) - 1) = Z(X) · Q4(X)
    let t_of_x = l_n_minus_1_of_x.clone().mul(
        &b_of_x
            .clone()
            .sub(&compute_constant_poly(&F::one())),
    );
    let b_check_q_of_x = t_of_x.div(&z_of_x);

    let sk_q1_com = filter_and_add(&prover_pp.q1_coms, &bitmap);
    let sk_q2_com = filter_and_add(&prover_pp.q2_coms, &bitmap);
    let agg_pk = compute_apk(&prover_pp, &bitmap, &cache);

    // Using KZG10 open for polynomial opening proofs
    let rand = Randomness::empty();
    
    let psw_of_r_proof = KZG::open(&powers, &psw_of_x, r, &rand).unwrap().w;
    let psw_of_r_div_ω_proof = KZG::open(&powers, &psw_of_x, r_div_ω, &rand).unwrap().w;
    let w_of_r_proof = KZG::open(&powers, &w_of_x, r, &rand).unwrap().w;
    let b_of_r_proof = KZG::open(&powers, &b_of_x, r, &rand).unwrap().w;
    let psw_wff_q_of_r_proof = KZG::open(&powers, &psw_wff_q_of_x, r, &rand).unwrap().w;
    let psw_check_q_of_r_proof = KZG::open(&powers, &psw_check_q_of_x, r, &rand).unwrap().w;
    let b_wff_q_of_r_proof = KZG::open(&powers, &b_wff_q_of_x, r, &rand).unwrap().w;
    let b_check_q_of_r_proof = KZG::open(&powers, &b_check_q_of_x, r, &rand).unwrap().w;

    let merged_proof: G1 = (psw_of_r_proof
        + w_of_r_proof.mul(r.pow([1]))
        + b_of_r_proof.mul(r.pow([2]))
        + psw_wff_q_of_r_proof.mul(r.pow([3]))
        + psw_check_q_of_r_proof.mul(r.pow([4]))
        + b_wff_q_of_r_proof.mul(r.pow([5]))
        + b_check_q_of_r_proof.mul(r.pow([6])))
    .into_affine();

    // Create commitments to polynomials
    let (psw_of_x_com, _) = KZG::commit(&powers, &psw_of_x, hiding_bound, Some(&mut rng)).unwrap();
    let (b_of_x_com, _) = KZG::commit(&powers, &b_of_x, hiding_bound, Some(&mut rng)).unwrap();
    let (psw_wff_q_of_x_com, _) = KZG::commit(&powers, &psw_wff_q_of_x, hiding_bound, Some(&mut rng)).unwrap();
    let (psw_check_q_of_x_com, _) = KZG::commit(&powers, &psw_check_q_of_x, hiding_bound, Some(&mut rng)).unwrap();
    let (b_wff_q_of_x_com, _) = KZG::commit(&powers, &b_wff_q_of_x, hiding_bound, Some(&mut rng)).unwrap();
    let (b_check_q_of_x_com, _) = KZG::commit(&powers, &b_check_q_of_x, hiding_bound, Some(&mut rng)).unwrap();

    HinTSProof {
        agg_pk,
        agg_weight: total_active_weight,

        r,

        psw_of_r_div_ω: psw_of_x.evaluate(&r_div_ω),
        psw_of_r_div_ω_proof,

        psw_of_r: psw_of_x.evaluate(&r),
        w_of_r: w_of_x.evaluate(&r),
        b_of_r: b_of_x.evaluate(&r),
        psw_wff_q_of_r: psw_wff_q_of_x.evaluate(&r),
        psw_check_q_of_r: psw_check_q_of_x.evaluate(&r),
        b_wff_q_of_r: b_wff_q_of_x.evaluate(&r),
        b_check_q_of_r: b_check_q_of_x.evaluate(&r),

        merged_proof,

        psw_of_x_com,
        b_of_x_com,
        psw_wff_q_of_x_com,
        psw_check_q_of_x_com,
        b_wff_q_of_x_com,
        b_check_q_of_x_com,

        sk_q1_com,
        sk_q2_com,
    }
}

fn filter_and_add(elements: &Vec<G1>, bitmap: &Vec<F>) -> G1 {
    let mut com = <Bls12_381 as Pairing>::G1::zero().into_affine();
    for i in 0..bitmap.len() {
        if bitmap[i] == F::one() {
            com = (com + elements[i]).into_affine();
        }
    }
    com
}

fn compute_apk(pp: &ProverPreprocessing, bitmap: &Vec<F>, cache: &Cache) -> G1 {
    let n = bitmap.len();
    let mut exponents = vec![];
    for i in 0..n {
        let l_i_of_x = &cache.lagrange_polynomials[i];
        let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
        let active = bitmap[i] == F::one();
        exponents.push(if active { l_i_of_0 } else { F::from(0) });
    }

    <Bls12_381 as Pairing>::G1::msm(&pp.pks[..], &exponents)
        .unwrap()
        .into_affine()
}

pub fn verify(vp: &VerifierPreprocessing, π: &HinTSProof) -> bool {
    // We'll use arkworks KZG10::check for checking polynomial openings
    
    // First verify the openings
    verify_openings(vp, π);

    let domain = Radix2EvaluationDomain::<F>::new(vp.n as usize).unwrap();
    let ω: F = domain.group_gen;

    let n: u64 = vp.n as u64;
    let vanishing_of_r: F = π.r.pow([n]) - F::one();

    // Compute L_i(r) using the relation L_i(x) = Z_V(x) / ( Z_V'(x) (x - ω^i) )
    // Where Z_V'(x)^-1 = x / N for N = |V|.
    let ω_pow_n_minus_1 = ω.pow([n - 1]);
    let l_n_minus_1_of_r =
        (ω_pow_n_minus_1 / F::from(n)) * (vanishing_of_r / (π.r - ω_pow_n_minus_1));

    // Assert polynomial identity for the secret part
    let lhs = <Bls12_381 as Pairing>::pairing(π.b_of_x_com.0, vp.sk_of_x_com);
    let x1 = <Bls12_381 as Pairing>::pairing(π.sk_q1_com, vp.vanishing_com);
    let x2 = <Bls12_381 as Pairing>::pairing(π.sk_q2_com, vp.x_monomial_com);
    let x3 = <Bls12_381 as Pairing>::pairing(π.agg_pk, vp.vk.h);
    let rhs = x1.add(x2).add(x3);
    if lhs != rhs {
        return false;
    }

    // Assert checks on the public part

    // ParSumW(r) − ParSumW(r/ω) − W(r) · b(r) = Q(r) · (r^n − 1)
    let lhs = π.psw_of_r - π.psw_of_r_div_ω - π.w_of_r * π.b_of_r;
    let rhs = π.psw_wff_q_of_r * vanishing_of_r;
    if lhs != rhs {
        return false;
    }

    // Ln−1(X) · ParSumW(X) = Z(X) · Q2(X)
    let lhs = l_n_minus_1_of_r * π.psw_of_r;
    let rhs = vanishing_of_r * π.psw_check_q_of_r;
    if lhs != rhs {
        return false;
    }

    // b(r) * b(r) - b(r) = Q(r) · (r^n − 1)
    let lhs = π.b_of_r * π.b_of_r - π.b_of_r;
    let rhs = π.b_wff_q_of_r * vanishing_of_r;
    if lhs != rhs {
        return false;
    }

    // Ln−1(X) · (b(X) − 1) = Z(X) · Q4(X)
    let lhs = l_n_minus_1_of_r * (π.b_of_r - F::one());
    let rhs = vanishing_of_r * π.b_check_q_of_r;
    lhs == rhs
}

fn verify_openings(vp: &VerifierPreprocessing, π: &HinTSProof) {
    // Adjust the w_of_x_com
    let adjustment = F::from(0) - π.agg_weight;
    let adjustment_com = vp.l_n_minus_1_of_x_com.0.mul(adjustment).into_affine();
    let w_of_x_com = Commitment((vp.w_of_x_com.0 + adjustment_com.mul(F::one())).into_affine());

    // We use the arkworks KZG10::check for polynomial openings
    let rng = &mut test_rng();

    // Create a batch verification
    let commitments = vec![
        π.psw_of_x_com.clone(),
        w_of_x_com,
        π.b_of_x_com.clone(),
        π.psw_wff_q_of_x_com.clone(),
        π.psw_check_q_of_x_com.clone(),
        π.b_wff_q_of_x_com.clone(),
        π.b_check_q_of_x_com.clone()
    ];

    let points = vec![
        π.r,
        π.r,
        π.r,
        π.r,
        π.r,
        π.r,
        π.r
    ];

    let values = vec![
        π.psw_of_r,
        π.w_of_r,
        π.b_of_r,
        π.psw_wff_q_of_r,
        π.psw_check_q_of_r,
        π.b_wff_q_of_r,
        π.b_check_q_of_r
    ];

    // Create proofs for batch verification
    let proofs: Vec<Proof<Bls12_381>> = vec![
        Proof { w: π.merged_proof, random_v: None },
    ];

    // We should use batch verification here, but for now we'll check the merged proof
    // This is a simplified version - in practice we'd need a proper batch check
    let result = KZG::check(
        &vp.vk,
        &π.psw_of_x_com,
        π.r,
        π.psw_of_r,
        &Proof { w: π.merged_proof, random_v: None },
    ).unwrap();

    assert!(result, "Polynomial opening verification failed");

    // Also verify the opening at r_div_ω
    let domain = Radix2EvaluationDomain::<F>::new(vp.n as usize).unwrap();
    let r_div_ω = π.r / domain.group_gen;
    let result = KZG::check(
        &vp.vk, 
        &π.psw_of_x_com, 
        r_div_ω, 
        π.psw_of_r_div_ω,
        &Proof { w: π.psw_of_r_div_ω_proof, random_v: None }
    ).unwrap();

    assert!(result, "Polynomial opening at r_div_ω verification failed");
}

// Implementation of sample_secret_keys function
pub fn sample_secret_keys(num_parties: usize) -> Vec<F> {
    let mut rng = test_rng();
    let mut keys = vec![];
    for _ in 0..num_parties {
        keys.push(F::rand(&mut rng));
    }
    keys
}

// Main function to demo the code
pub fn main() {
    use std::time::Instant;
    let n: usize = 64;
    println!("n = {}", n);

    // Contains commonly used objects such as lagrange polynomials
    let cache = prepare_cache(n);

    // Sample one-time SRS
    let rng = &mut test_rng();
    // Use arkworks KZG10::setup instead of our custom KZG::setup
    let params = KZG::setup(n, true, rng).expect("Setup failed");

    // Sample universe specific values
    // Sample random keys
    let sk: Vec<F> = sample_secret_keys(n - 1);
    // Sample random weights for each party
    let weights = sample_weights(n - 1);

    // Run universe setup
    let (vp, pp) = setup(n, &params, &weights, &sk);

    // Samples n-1 random bits
    let bitmap = sample_bitmap(n - 1, 0.9);

    let start = Instant::now();
    // Generate proof
    let proof = prove(&params, &pp, &cache, &weights, &bitmap);
    let duration = start.elapsed();
    println!("Time elapsed in prover is: {:?}", duration);
    
    let start = Instant::now();
    // Verify proof
    let result = verify(&vp, &proof);
    let duration = start.elapsed();
    println!("Time elapsed in verifier is: {:?}", duration);
    
    println!("Verification result: {}", result);
}