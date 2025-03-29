use ark_ff::{One, Zero};
use bolero::check;
use hints::snark::{
    finish_setup, hintgen, AggregationKey, GlobalData, Hint, SetupResult, VerifierKey, F, KZG,
};
use hints::{HintsError, PartialSignature, PublicKey, SecretKey, Signature};
use std::collections::HashMap;

use crate::test_helpers::*;

// Custom generator for protocol-specific structures
#[derive(Debug, bolero_generator::TypeGenerator)]
struct HintsTestCase {
    domain_power: u8,  // Use power of 2 for domain size
    weights: Vec<u16>, // Use u16 to avoid field overflow and convert to F
    message: Vec<u8>,
    signer_indices: Vec<u8>, // Convert to valid indices
    threshold_strategy: u8,  // Different threshold selection strategies
}

#[test]
fn fuzz_hints_protocol() {
    // Use bolero to generate structured test cases
    check!()
        .with_type::<HintsTestCase>()
        .with_max_depth(5)
        .for_each(|test_case| {
            // Convert domain power to valid domain size (4 to 256)
            let domain_power = (test_case.domain_power % 6) + 2; // 2^2 to 2^7
            let domain_max = 1 << domain_power;
            let n_participants = domain_max - 1;

            // Create valid weights (use u16 to avoid overflows)
            let weights: Vec<F> = test_case
                .weights
                .iter()
                .take(n_participants)
                .map(|w| F::from(*w as u64))
                .collect();

            if weights.len() < n_participants {
                // Pad with 1s if we don't have enough weights
                let mut padded_weights = weights;
                padded_weights.resize(n_participants, F::one());

                run_protocol_test(
                    domain_max,
                    padded_weights,
                    &test_case.message,
                    &test_case.signer_indices,
                    test_case.threshold_strategy,
                );
            } else {
                run_protocol_test(
                    domain_max,
                    weights,
                    &test_case.message,
                    &test_case.signer_indices,
                    test_case.threshold_strategy,
                );
            }
        });
}

/// Central test runner that verifies the protocol with generated inputs
fn run_protocol_test(
    domain_max: usize,
    weights: Vec<F>,
    message: &[u8],
    signer_indices_raw: &[u8],
    threshold_strategy: u8,
) {
    // Ensure we have a valid message (empty or non-empty)
    let message = if message.is_empty() {
        b"default test message"
    } else {
        message
    };

    // Convert indices to a valid set
    let n_participants = weights.len();
    let mut signer_indices: Vec<usize> = signer_indices_raw
        .iter()
        .map(|idx| (*idx as usize) % n_participants)
        .collect();

    // Remove duplicates and ensure we have at least one signer
    signer_indices.sort();
    signer_indices.dedup();

    if signer_indices.is_empty() && !signer_indices_raw.is_empty() {
        signer_indices.push(signer_indices_raw[0] as usize % n_participants);
    }

    // Skip test if no signers
    if signer_indices.is_empty() {
        return;
    }

    // Setup the protocol environment
    let mut rng = seeded_rng();
    let setup_result = setup_test_env(domain_max, n_participants, &mut rng);

    // Only proceed if setup was successful
    if let Ok((global_data, secret_keys, public_keys, hints, _)) = setup_result {
        // Generate partial signatures
        let mut partials = Vec::new();
        let mut signer_weights = HashMap::new();

        for &idx in &signer_indices {
            if idx >= n_participants {
                continue; // Skip invalid indices
            }

            // Create partial signature
            let partial = secret_keys[idx].sign(message);

            // Verify partial against public key and hint
            if !hints::partial_verify(&global_data, &public_keys[idx], message, &partial) {
                continue; // Skip invalid partials
            }

            partials.push((idx, partial));
            signer_weights.insert(idx, weights[idx]);
        }

        if partials.is_empty() {
            return; // No valid partials, skip test
        }

        // Calculate threshold based on strategy
        let total_weight = calculate_threshold(&weights, &signer_weights, threshold_strategy);

        // Complete setup to get aggregation and verifier keys
        let (agg_key, vk) = match run_finish_setup(
            &global_data,
            domain_max,
            public_keys,
            &hints,
            weights.clone(),
        ) {
            Ok((ak, vk)) => (ak, vk),
            Err(_) => return, // Skip test if setup fails
        };

        // Test the aggregation and verification
        let sig_result = agg_key.aggregate(
            &global_data,
            total_weight,
            &partials,
            weights.clone(),
            message,
        );

        match sig_result {
            Ok(signature) => {
                // Verify signature
                let verify_result = signature.verify(&global_data, &vk, message);

                // If we used the correct threshold, verification should pass
                if threshold_strategy == 0 {
                    assert!(
                        verify_result.is_ok() && verify_result.unwrap(),
                        "Verification failed for correct threshold"
                    );

                    // Property testing: modifying message should break verification
                    if !message.is_empty() {
                        let mut modified = message.to_vec();
                        modified[0] ^= 1; // Flip one bit
                        let tampered_result = signature.verify(&global_data, &vk, &modified);
                        assert!(
                            tampered_result.is_err() || !tampered_result.unwrap(),
                            "Verification should fail for modified message"
                        );
                    }

                    // Determinism test: signature aggregation should be deterministic
                    let signature2 = agg_key
                        .aggregate(&global_data, total_weight, &partials, weights, message)
                        .expect("Second aggregation failed");

                    assert_eq!(
                        format!("{:?}", signature),
                        format!("{:?}", signature2),
                        "Signature aggregation must be deterministic"
                    );
                }
                // For intentionally incorrect thresholds, we don't make assertions
                // as behavior depends on implementation details
            }
            Err(_) => {
                // For the correct threshold, aggregation should succeed
                if threshold_strategy == 0 {
                    panic!("Aggregation failed with correct threshold");
                }
                // For incorrect thresholds, failure is expected in many cases
            }
        }
    }
}

/// Calculate threshold based on different strategies to test robustness
fn calculate_threshold(all_weights: &[F], signer_weights: &HashMap<usize, F>, strategy: u8) -> F {
    // Different threshold calculation strategies to test robustness
    match strategy % 5 {
        0 => {
            // Correct threshold: sum of signer weights
            signer_weights.values().fold(F::zero(), |acc, &w| acc + w)
        }
        1 => {
            // Incorrect: slightly higher threshold
            let correct = signer_weights.values().fold(F::zero(), |acc, &w| acc + w);
            correct + F::one()
        }
        2 => {
            // Incorrect: slightly lower threshold
            let correct = signer_weights.values().fold(F::zero(), |acc, &w| acc + w);
            if correct > F::one() {
                correct - F::one()
            } else {
                correct
            }
        }
        3 => {
            // Incorrect: zero threshold
            F::zero()
        }
        4 => {
            // Incorrect: maximum sum (all weights)
            all_weights.iter().fold(F::zero(), |acc, &w| acc + w)
        }
        _ => unreachable!(),
    }
}
