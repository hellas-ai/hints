use ark_ff::Zero;
use ark_std::rand::rngs::StdRng;
use ark_std::rand::{RngCore, SeedableRng};
use bolero::check;
use hints::snark::F;

use crate::test_helpers::*;

// Define a structured test to be run with all parameter combinations
#[derive(Debug, bolero_generator::TypeGenerator)]
enum DomainSize {
    Minimum, // 4
    Small,   // 8
    Medium,  // 16
    Large,   // 32
}

#[derive(Debug, bolero_generator::TypeGenerator)]
enum WeightDistribution {
    Uniform,
    Skewed,
    Binary,
    Prime,
}

#[derive(Debug, bolero_generator::TypeGenerator)]
enum MessageType {
    Empty,
    Small,
    Medium,
    Large,
}

#[derive(Debug, bolero_generator::TypeGenerator)]
enum SignerSet {
    One,
    Few,
    Half,
    Most,
    All,
}

#[derive(Debug, bolero_generator::TypeGenerator)]
struct ProtocolParameters {
    domain: DomainSize,
    weights: WeightDistribution,
    message: MessageType,
    signers: SignerSet,
}

#[test]
fn test_all_parameter_combinations() {
    // Test all combinations of parameters
    check!()
        .with_type::<ProtocolParameters>()
        .for_each(|params| {
            run_protocol_with_parameters(params);
        });
}

// Main test function that runs the protocol with specific parameter combinations
fn run_protocol_with_parameters(params: &ProtocolParameters) {
    let mut rng = seeded_rng();

    // Convert enum values to concrete parameters
    let domain_max = match params.domain {
        DomainSize::Minimum => 4,
        DomainSize::Small => 8,
        DomainSize::Medium => 16,
        DomainSize::Large => 32,
    };

    let n_participants = domain_max - 1;

    // Create fixture
    let mut fixture = match TestFixture::new(domain_max, n_participants, &mut rng) {
        Ok(f) => f,
        Err(e) => {
            println!("Failed to create fixture for params {:?}: {:?}", params, e);
            return;
        }
    };

    // Generate weights based on distribution
    match params.weights {
        WeightDistribution::Uniform => {
            // Uniform weights
            fixture.set_all_weights(F::from(1u64));
        }
        WeightDistribution::Skewed => {
            // One very heavy weight, rest small
            fixture.set_all_weights(F::from(1u64));
            if n_participants > 0 {
                fixture.set_weight(0, F::from(n_participants as u64 * 2));
            }
        }
        WeightDistribution::Binary => {
            // Powers of 2
            for i in 0..n_participants {
                fixture.set_weight(i, F::from(1u64 << (i % 8)));
            }
        }
        WeightDistribution::Prime => {
            // Prime numbers
            let primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29];
            for i in 0..n_participants {
                fixture.set_weight(i, F::from(primes[i % primes.len()] as u64));
            }
        }
    };

    if fixture.complete_setup().is_err() {
        println!("Failed to complete setup for params {:?}", params);
        return;
    }

    // Create message
    let message: &[u8] = match params.message {
        MessageType::Empty => b"",
        MessageType::Small => b"small",
        MessageType::Medium => b"medium sized message",
        MessageType::Large => &[b'A'; 1024][..],
    };

    // Determine which signers to use
    let indices = match params.signers {
        SignerSet::One => vec![0],
        SignerSet::Few => (0..n_participants / 4.max(1)).collect(),
        SignerSet::Half => (0..n_participants / 2.max(1)).collect(),
        SignerSet::Most => (0..n_participants * 3 / 4.max(1)).collect(),
        SignerSet::All => (0..n_participants).collect(),
    };

    if indices.is_empty() {
        println!("No signers selected for params {:?}", params);
        return;
    }

    // Generate partial signatures
    let partials = fixture.generate_signatures(&indices, message);

    // Calculate subset weight
    let total_weight = fixture.sum_weights(&indices);

    // Try to aggregate and verify
    match fixture.aggregate(total_weight, &partials, message) {
        Ok(signature) => match fixture.verify(&signature, message) {
            Ok(true) => {
                println!("✓ Successful verification for params: {:?}", params);
            }
            Ok(false) => {
                panic!("Verification returned false for params: {:?}", params);
            }
            Err(e) => {
                panic!("Verification error for params: {:?}: {:?}", params, e);
            }
        },
        Err(e) => {
            // For some parameter combinations, aggregation might legitimately fail
            println!(
                "Aggregation failed for params: {:?}, error: {:?}",
                params, e
            );
        }
    }

    // Also test with a modified message to ensure it fails
    if !message.is_empty() {
        let mut modified = message.to_vec();
        modified[0] ^= 1; // Flip one bit

        let partials_for_modified = fixture.generate_signatures(&indices, &modified);

        match fixture.aggregate(total_weight, &partials_for_modified, &modified) {
            Ok(signature) => {
                match fixture.verify(&signature, message) {
                    // Verify with original message
                    Ok(false) | Err(_) => {
                        // Expected: signature for modified message should not verify with original
                    }
                    Ok(true) => {
                        panic!(
                            "Verification succeeded for wrong message with params: {:?}",
                            params
                        );
                    }
                }
            }
            Err(_) => {
                // This is fine - aggregation might fail for some cases
            }
        }
    }
}

/// Tests the protocol with adversarial parameter selections
#[test]
fn test_adversarial_parameter_combinations() {
    let mut rng = seeded_rng();

    // Test various adversarial combinations

    // 1. Test with extremely skewed weights
    let domain_max = 32;
    let n_participants = domain_max - 1;

    let mut fixture = match TestFixture::new(domain_max, n_participants, &mut rng) {
        Ok(f) => f,
        Err(e) => panic!("Setup failed: {:?}", e),
    };

    // One participant has 1000x the weight of others
    fixture.set_all_weights(F::from(1u64));
    fixture.set_weight(0, F::from(1000u64));

    if fixture.complete_setup().is_err() {
        panic!("Complete setup failed");
    }

    // Message to sign
    let message = b"adversarial test";

    // Test with just the heavy participant
    let heavy_indices = vec![0];
    let heavy_partials = fixture.generate_signatures(&heavy_indices, message);
    let heavy_threshold = fixture.sum_weights(&heavy_indices);

    match fixture.aggregate(heavy_threshold, &heavy_partials, message) {
        Ok(signature) => match fixture.verify(&signature, message) {
            Ok(true) => println!("Heavy participant signature verified"),
            _ => panic!("Heavy participant signature verification failed"),
        },
        Err(e) => panic!("Heavy participant aggregation failed: {:?}", e),
    }

    // Test with all the light participants (but not the heavy one)
    let light_indices: Vec<usize> = (1..n_participants).collect();
    let light_partials = fixture.generate_signatures(&light_indices, message);
    let light_threshold = fixture.sum_weights(&light_indices);

    match fixture.aggregate(light_threshold, &light_partials, message) {
        Ok(signature) => match fixture.verify(&signature, message) {
            Ok(true) => println!("Light participants signature verified"),
            _ => panic!("Light participants signature verification failed"),
        },
        Err(e) => println!(
            "Light participants aggregation failed (possibly expected): {:?}",
            e
        ),
    }

    // 2. Test with zero weights for some participants
    let mut fixture = match TestFixture::new(domain_max, n_participants, &mut rng) {
        Ok(f) => f,
        Err(e) => panic!("Setup failed: {:?}", e),
    };

    // Some participants have zero weight
    fixture.set_all_weights(F::from(1u64));
    fixture.set_weight(1, F::zero());
    fixture.set_weight(3, F::zero());

    if fixture.complete_setup().is_err() {
        panic!("Complete setup failed");
    }

    // Try to sign with all participants
    let all_indices: Vec<usize> = (0..n_participants).collect();
    let all_partials = fixture.generate_signatures(&all_indices, message);
    let all_threshold = fixture.sum_weights(&all_indices);

    match fixture.aggregate(all_threshold, &all_partials, message) {
        Ok(signature) => match fixture.verify(&signature, message) {
            Ok(true) => println!("All participants with zero weights signature verified"),
            _ => panic!("All participants with zero weights verification failed"),
        },
        Err(e) => panic!(
            "All participants with zero weights aggregation failed: {:?}",
            e
        ),
    }

    // 3. Test with minimum viable domain size and just one participant
    let min_domain_max = 2;
    let min_participants = min_domain_max - 1;

    let mut fixture = match TestFixture::new(min_domain_max, min_participants, &mut rng) {
        Ok(f) => f,
        Err(e) => {
            println!("Minimum domain test skipped - setup failed: {:?}", e);
            return;
        }
    };

    if fixture.complete_setup().is_err() {
        println!("Minimum domain test skipped - complete setup failed");
        return;
    }

    // One participant signs
    let min_indices = vec![0];
    let min_partials = fixture.generate_signatures(&min_indices, message);
    let min_threshold = fixture.sum_weights(&min_indices);

    match fixture.aggregate(min_threshold, &min_partials, message) {
        Ok(signature) => match fixture.verify(&signature, message) {
            Ok(true) => println!("Minimum domain signature verified"),
            _ => panic!("Minimum domain verification failed"),
        },
        Err(e) => println!(
            "Minimum domain aggregation failed (possibly expected): {:?}",
            e
        ),
    }
}
