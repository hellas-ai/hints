use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use hints::snark::*;
use hints::*;

use ark_poly::DenseUVPolynomial;
use ark_std::*;

use serde::{Deserialize, Serialize};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

#[serde_with::serde_as]
#[derive(Serialize, Deserialize)]
struct Committee {
    pub pks: Vec<PublicKey>,
    #[serde_as(as = "Vec<ark_serialize::CompressedChecked<F>>")]
    pub weights: Vec<F>,
    pub hints: Vec<Hint>,
    pub sks: Vec<SecretKey>,
    pub setup: UniverseSetup,
}

const BIG_COMMITTEE: &str = include_str!("big_committee.json");

// Helper function to sample random secret keys
fn sample_secret_keys(num_parties: usize) -> Vec<SecretKey> {
    let mut rng = test_rng();
    let mut keys = vec![];
    for _ in 0..num_parties {
        keys.push(SecretKey::random(&mut rng));
    }
    keys
}

// Helper function to sample random weights
fn sample_weights(n: usize) -> Vec<F> {
    let mut rng = &mut test_rng();
    (0..n).map(|_| F::from(u64::rand(&mut rng))).collect()
}

// Helper function to generate a random bitmap with a specific probability of 1s
fn sample_bitmap(n: usize, probability: f64) -> Vec<F> {
    let mut rng = &mut test_rng();
    let mut bitmap = vec![];
    for _i in 0..n {
        let r = f64::rand(&mut rng);
        if r < probability {
            bitmap.push(F::one());
        } else {
            bitmap.push(F::zero());
        }
    }
    bitmap
}

// Setup benchmarks
fn setup_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("KZG_setup");

    for size in [4, 8, 16, 32, 64].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_function(BenchmarkId::new("setup_insecure", size), |b| {
            let rng = &mut ark_std::test_rng();
            b.iter(|| GlobalData::new(*size, rng).expect("Insecure setup failed"));
        });
    }

    group.bench_function("setup_eth", |b| {
        b.iter(|| setup_eth(64).expect("Ethereum setup failed"));
    });

    group.finish();
}

// Key generation and signature benchmarks
fn key_signature_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("keys_signatures");
    let rng = &mut ark_std::test_rng();

    // Create global data for benchmarks
    let n = 128;
    let gd =
        GlobalData::from_params(KZG::setup(n, rng).expect("Setup failed")).expect("Setup failed");

    group.bench_function("generate_keypair", |b| {
        b.iter(|| generate_keypair(&gd, rng));
    });

    let (sk, _) = generate_keypair(&gd, rng);
    let message = b"benchmark message";

    group.bench_function("sign", |b| {
        b.iter(|| sign(&sk, message));
    });

    let pk = sk.public(&gd);
    let sig = sign(&sk, message);

    group.bench_function("verify_partial", |b| {
        b.iter(|| verify_partial(&gd, &pk, message, &sig));
    });

    group.finish();
}

// SNARK benchmarks
fn snark_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("snark");

    let rng = &mut ark_std::test_rng();
    let biggest = KZG::setup(128, rng).expect("Setup failed");

    for size in [16, 32, 64, 128].iter() {
        let n = *size;

        let mut params = biggest.clone();
        params.truncate(n);

        // Setup
        let gd = GlobalData::from_params(params).expect("Setup failed");

        // Keys and weights
        let sk: Vec<SecretKey> = sample_secret_keys(n - 1);
        let pks: Vec<PublicKey> = sk.iter().map(|sk| sk.public(&gd)).collect();
        let weights = sample_weights(n - 1);

        let hints: Vec<Hint> = sk
            .par_iter()
            .enumerate()
            .map(|(i, sk)| generate_hint(&gd, sk, n, i).expect("Failed to generate hints"))
            .collect();

        // Setup
        let univ = setup_universe(&gd, pks.clone(), &hints, weights.clone())
            .expect("Failed to finish setup");

        // Benchmarks for hint generation
        group.throughput(Throughput::Elements(n as u64));

        group.bench_function(BenchmarkId::new("generate_hint", n), |b| {
            b.iter(|| generate_hint(&gd, &sk[0], n, n - 1).expect("Failed to generate hint"));
        });

        group.bench_function(BenchmarkId::new("finish_setup", n), |b| {
            b.iter(|| {
                setup_universe(&gd, pks.clone(), &hints, weights.clone())
                    .expect("Failed to finish setup")
            });
        });

        // Sample bitmap
        let bitmap = sample_bitmap(n - 1, 0.9);

        group.bench_function(BenchmarkId::new("prove", n), |b| {
            b.iter(|| {
                prove(&gd, &univ.agg_key, &weights, &bitmap).expect("Failed to generate proof")
            });
        });

        let proof = prove(&gd, &univ.agg_key, &weights, &bitmap).expect("Failed to generate proof");

        if n == 16 {
            // these are unparameterized but need the setup done, just do them once
            group.bench_function("verify_proof", |b| {
                b.iter(|| verify_proof(&gd, &univ.vk, &proof).expect("Proof is invalid"));
            });

            group.bench_function("compute_challenge_r", |b| {
                let protocol = lockstitch::Protocol::new("hints benchmark domain");

                b.iter(|| {
                    let proto = protocol.clone();
                    snark::compute_challenge_r(
                        &proto,
                        &univ.vk.0,
                        &proof.agg_pk,
                        &proof.agg_weight,
                        &proof.coms,
                    )
                });
            });
        }
    }

    let big_committee: Committee =
        serde_json::from_str(BIG_COMMITTEE).expect("Failed to parse committee");

    let n = big_committee.pks.len();

    group.bench_function(BenchmarkId::new("generate_hint", n), |b| {
        b.iter(|| {
            generate_hint(&big_committee.setup.global, &big_committee.sks[0], n, n - 1)
                .expect("Failed to generate hint")
        });
    });

    group.bench_function(BenchmarkId::new("finish_setup", n), |b| {
        b.iter(|| {
            setup_universe(
                &big_committee.setup.global,
                big_committee.pks.clone(),
                &big_committee.hints,
                big_committee.weights.clone(),
            )
            .expect("Failed to finish setup")
        });
    });

    group.finish();
}

// Aggregation benchmarks
fn aggregation_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("aggregation");

    for size in [16, 32, 64, 128].iter() {
        let n = *size;
        let rng = &mut ark_std::test_rng();

        // Setup
        let gd = GlobalData::from_params(KZG::setup(n, rng).expect("Setup failed"))
            .expect("Setup failed");

        // Keys and weights
        let sk: Vec<SecretKey> = sample_secret_keys(n - 1);
        let pks: Vec<PublicKey> = sk.iter().map(|sk| sk.public(&gd)).collect();
        let weights = sample_weights(n - 1);

        let hints: Vec<Hint> = sk
            .par_iter()
            .enumerate()
            .map(|(i, sk)| generate_hint(&gd, sk, n, i).expect("Failed to generate hints"))
            .collect();

        // Setup
        let univ = setup_universe(&gd, pks.clone(), &hints, weights.clone())
            .expect("Failed to finish setup");

        // Message
        let message = b"benchmark message";

        // Partial signatures
        let partials: Vec<(usize, PartialSignature)> = sk
            .iter()
            .enumerate()
            .map(|(i, sk)| (i, sign(sk, message)))
            .collect();

        group.throughput(Throughput::Elements(n as u64));

        let agg = univ.aggregator();
        let verif = univ.verifier();

        group.bench_function(BenchmarkId::new("sign_aggregate_unchecked", n), |b| {
            b.iter(|| {
                sign_aggregate_unchecked(&agg, F::one(), &partials, message)
                    .expect("Failed to aggregate signatures")
            });
        });

        let sig = sign_aggregate(&agg, F::one(), &partials, message)
            .expect("Failed to aggregate signatures");

        group.bench_function(BenchmarkId::new("verify_aggregate", n), |b| {
            b.iter(|| verify_aggregate(&verif, &sig, message).expect("Signature is invalid"));
        });
    }

    let big_committee: Committee =
        serde_json::from_str(BIG_COMMITTEE).expect("Failed to parse committee");

    let n = big_committee.pks.len();
    // Message
    let message = b"benchmark message";

    // Partial signatures
    let partials: Vec<(usize, PartialSignature)> = big_committee
        .sks
        .iter()
        .enumerate()
        .map(|(i, sk)| (i, sign(sk, message)))
        .collect();

    let agg = big_committee.setup.aggregator();
    let verif = big_committee.setup.verifier();

    let sig = sign_aggregate(&agg, F::one(), &partials, message)
        .expect("Failed to aggregate signatures");

    group.bench_function(BenchmarkId::new("verify_aggregate", n), |b| {
        b.iter(|| verify_aggregate(&verif, &sig, message).expect("Signature is invalid"));
    });
    group.bench_function(BenchmarkId::new("sign_aggregate_unchecked", 1024), |b| {
        b.iter(|| {
            sign_aggregate_unchecked(&agg, F::one(), &partials, message)
                .expect("Failed to aggregate signatures")
        });
    });

    group.finish();
}

// KZG polynomial operations benchmarks
fn kzg_operations_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("kzg_operations");

    let rng = &mut ark_std::test_rng();

    for n in [64, 1024, 8192, 8192 * 4].iter().copied() {
        let params = KZG::setup(n, rng).expect("Setup failed");

        // Create a random polynomial
        let coeffs: Vec<F> = (0..n).map(|_| F::rand(rng)).collect();
        let poly = UniPoly381::from_coefficients_slice(&coeffs);

        group.bench_function(BenchmarkId::new("commit_g1", n), |b| {
            b.iter(|| KZG::commit_g1(&params, &poly).expect("Failed to commit"));
        });

        group.bench_function(BenchmarkId::new("commit_g2", n), |b| {
            b.iter(|| KZG::commit_g2(&params, &poly).expect("Failed to commit"));
        });

        // Random evaluation point
        let point = F::rand(rng);

        group.bench_function(BenchmarkId::new("compute_opening_proof", n), |b| {
            b.iter(|| {
                KZG::compute_opening_proof(&params, &poly, &point)
                    .expect("Failed to compute opening proof")
            });
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    setup_benchmarks,
    key_signature_benchmarks,
    snark_benchmarks,
    aggregation_benchmarks,
    kzg_operations_benchmarks,
);
criterion_main!(benches);
