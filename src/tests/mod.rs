#![allow(dead_code)]

//! Consolidated test suite for the Hints protocol implementation.
//! Uses a table-driven approach with a single test function to reduce boilerplate.

use crate::HintsError;
use ark_std::{One, UniformRand};
use std::fmt;

mod harness;
use harness::*;

/// Test case definition for table-driven testing
struct TestCase {
    /// Unique name for the test
    name: &'static str,
    /// Test configuration
    config: TestConfig,
    /// Expected outcome
    expected: ExpectedOutcome,
    /// Optional description for clarity
    description: Option<&'static str>,
}

/// Configuration for a test case
#[derive(Clone)]
struct TestConfig {
    domain_power: u32,
    weight_strategy: WeightStrategy,
    signers: Vec<usize>,
    message: Vec<u8>,
    threshold_strategy: ThresholdStrategy,
}

impl Default for TestConfig {
    fn default() -> Self {
        Self {
            domain_power: 3, // 2^3 = 8 by default
            weight_strategy: WeightStrategy::Uniform(1),
            signers: vec![0, 1, 2],
            message: b"test message".to_vec(),
            threshold_strategy: ThresholdStrategy::Exact,
        }
    }
}

impl fmt::Debug for TestCase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

/// The single test function that runs all test cases
#[test]
fn run_all_tests() {
    // Zero weight indices for reuse
    static ZERO_INDICES: [usize; 2] = [1, 3];

    // Create a performance tracker for timing analysis
    let tracker = PerformanceTracker::new();

    // Define all test cases
    let test_cases = vec![
        // === Edge Cases ===
        TestCase {
            name: "minimum_domain_size",
            config: TestConfig {
                domain_power: 1,  // Domain size 2 (minimum valid)
                signers: vec![0], // Only one participant
                message: b"minimum domain test".to_vec(),
                ..Default::default()
            },
            expected: ExpectedOutcome::Success,
            description: Some("Test with domain_max = 2 (smallest valid power of 2)"),
        },
        TestCase {
            name: "zero_weight_participants",
            config: TestConfig {
                weight_strategy: WeightStrategy::WithZeros {
                    default: 1,
                    zero_indices: &ZERO_INDICES,
                },
                signers: (0..7).collect(), // All participants
                message: b"zero weight test".to_vec(),
                ..Default::default()
            },
            expected: ExpectedOutcome::Success,
            description: Some("Test with some participants having zero weight"),
        },
        TestCase {
            name: "zero_weight_participants_nonzero_only",
            config: TestConfig {
                weight_strategy: WeightStrategy::WithZeros {
                    default: 1,
                    zero_indices: &ZERO_INDICES,
                },
                signers: vec![0, 2, 4, 5, 6], // Only non-zero participants
                message: b"zero weight test - non-zero only".to_vec(),
                ..Default::default()
            },
            expected: ExpectedOutcome::Success,
            description: Some("Test with only non-zero weight participants signing"),
        },
        TestCase {
            name: "extremely_skewed_weights_dominant",
            config: TestConfig {
                weight_strategy: WeightStrategy::Skewed {
                    dominant_idx: 0,
                    dominant_weight: 1000000,
                    others: 1,
                },
                signers: vec![0], // Just the dominant participant
                message: b"skewed weight test".to_vec(),
                ..Default::default()
            },
            expected: ExpectedOutcome::Success,
            description: Some("Test with extremely skewed weights - only dominant participant"),
        },
        TestCase {
            name: "extremely_skewed_weights_minors",
            config: TestConfig {
                weight_strategy: WeightStrategy::Skewed {
                    dominant_idx: 0,
                    dominant_weight: 1000000,
                    others: 1,
                },
                signers: vec![1, 2, 3, 4, 5, 6], // All except dominant
                message: b"skewed weight test - minors only".to_vec(),
                ..Default::default()
            },
            expected: ExpectedOutcome::Success,
            description: Some("Test with extremely skewed weights - only minor participants"),
        },
        TestCase {
            name: "empty_message",
            config: TestConfig {
                domain_power: 2,     // 2^2 = 4
                message: Vec::new(), // Empty message
                ..Default::default()
            },
            expected: ExpectedOutcome::Success,
            description: Some("Test with empty message"),
        },
        TestCase {
            name: "granular_threshold_error",
            config: TestConfig {
                domain_power: 2,                                 // 2^2 = 4
                signers: vec![0],                                // Just one participant
                threshold_strategy: ThresholdStrategy::Above(1), // Just above available
                ..Default::default()
            },
            expected: ExpectedOutcome::ThresholdNotMet,
            description: Some("Test with threshold just slightly higher than available"),
        },
        // === Integration Tests ===
        TestCase {
            name: "full_workflow_success",
            config: TestConfig {
                domain_power: 2,        // 2^2 = 4
                signers: vec![0, 1, 2], // All participants
                message: b"hello world".to_vec(),
                ..Default::default()
            },
            expected: ExpectedOutcome::Success,
            description: Some("Test complete workflow with all participants"),
        },
        TestCase {
            name: "subset_signs_success",
            config: TestConfig {
                domain_power: 3,        // 2^3 = 8
                signers: vec![0, 2, 4], // Subset of participants
                ..Default::default()
            },
            expected: ExpectedOutcome::Success,
            description: Some("Test with only a subset of participants signing"),
        },
        TestCase {
            name: "threshold_not_met_aggregation_fails",
            config: TestConfig {
                domain_power: 2,                                 // 2^2 = 4
                signers: vec![0],                                // Just one participant
                threshold_strategy: ThresholdStrategy::Above(1), // More than available
                ..Default::default()
            },
            expected: ExpectedOutcome::ThresholdNotMet,
            description: Some("Test threshold not met error with insufficient signers"),
        },
        TestCase {
            name: "wrong_message_verification_fails",
            config: TestConfig {
                domain_power: 2,        // 2^2 = 4
                signers: vec![0, 1, 2], // All participants
                message: b"original message".to_vec(),
                // Special handling in execute_test_case for message verification
                ..Default::default()
            },
            expected: ExpectedOutcome::VerificationFailed,
            description: Some("Test that verification fails with wrong message"),
        },
        TestCase {
            name: "tampered_signature_fails",
            config: TestConfig {
                domain_power: 2,        // 2^2 = 4
                signers: vec![0, 1, 2], // All participants
                // Special handling in execute_test_case for signature tampering
                ..Default::default()
            },
            expected: ExpectedOutcome::VerificationFailed,
            description: Some("Test that tampered signature fails verification"),
        },
        TestCase {
            name: "tampered_partial_negates_threshold_fails",
            config: TestConfig {
                domain_power: 2,        // 2^2 = 4
                signers: vec![0, 1, 2], // All participants
                // Special handling in execute_test_case for signature tampering
                ..Default::default()
            },
            expected: ExpectedOutcome::VerificationFailed,
            description: Some("Test that tampered signature fails verification"),
        },
        TestCase {
            name: "tampered_partial_maintains_threshold_success",
            config: TestConfig {
                domain_power: 2,        // 2^2 = 4
                signers: vec![0, 1, 2], // All participants
                // Special handling in execute_test_case for signature tampering
                ..Default::default()
            },
            expected: ExpectedOutcome::Success,
            description: Some("Test that tampered signature fails verification"),
        },
        TestCase {
            name: "binary_weight_distribution",
            config: TestConfig {
                domain_power: 3, // 2^3 = 8
                weight_strategy: WeightStrategy::Binary,
                signers: vec![0, 1, 2, 3], // First few participants
                ..Default::default()
            },
            expected: ExpectedOutcome::Success,
            description: Some("Test with binary weight distribution (powers of 2)"),
        },
        TestCase {
            name: "random_weight_distribution",
            config: TestConfig {
                domain_power: 3, // 2^3 = 8
                weight_strategy: WeightStrategy::Random { min: 1, max: 100 },
                signers: vec![0, 2, 4, 6], // Mixed participants
                ..Default::default()
            },
            expected: ExpectedOutcome::Success,
            description: Some("Test with random weight distribution"),
        },
        TestCase {
            name: "partial_threshold_percentage_meets",
            config: TestConfig {
                domain_power: 3,                                       // 2^3 = 8
                signers: vec![0, 1, 2, 3],                             // Half of participants
                threshold_strategy: ThresholdStrategy::Percentage(50), // 50% of total weight
                ..Default::default()
            },
            expected: ExpectedOutcome::Success,
            description: Some("Test with threshold as percentage of total weight"),
        },
        TestCase {
            name: "partial_threshold_percentage_exceeds",
            config: TestConfig {
                domain_power: 3,                                       // 2^3 = 8
                signers: vec![0, 1, 2, 3, 4],                          // Half of participants
                threshold_strategy: ThresholdStrategy::Percentage(50), // 50% of total weight
                ..Default::default()
            },
            expected: ExpectedOutcome::Success,
            description: Some("Test with threshold as percentage of total weight"),
        },
        TestCase {
            name: "large_domain_moderate_signers",
            config: TestConfig {
                domain_power: 5,            // 2^5 = 32
                signers: (0..10).collect(), // Only 10 out of 31 participants
                ..Default::default()
            },
            expected: ExpectedOutcome::Success,
            description: Some("Test with larger domain but moderate number of signers"),
        },
        TestCase {
            name: "custom_weight_distribution",
            config: TestConfig {
                domain_power: 3, // 2^3 = 8
                weight_strategy: WeightStrategy::Custom(vec![5, 10, 15, 20, 25, 30, 35]),
                signers: vec![2, 4, 6], // Mixed weights
                ..Default::default()
            },
            expected: ExpectedOutcome::Success,
            description: Some("Test with custom defined weights"),
        },
        // === Special Empty Partials Test ===
        // This one requires special handling
        TestCase {
            name: "empty_partials_aggregation",
            config: TestConfig {
                domain_power: 2, // 2^2 = 4
                signers: vec![], // No signers (empty partials)
                ..Default::default()
            },
            expected: ExpectedOutcome::ThresholdNotMet,
            description: Some("Test with no partial signatures (empty partials)"),
        },
    ];

    // Run all test cases
    let mut failed = 0;
    let mut skipped = 0;
    let total = test_cases.len();

    for test_case in test_cases {
        if test_case.name == "large_domain_size_scaling"
            && std::env::var("RUN_EXPENSIVE_TESTS").is_err()
        {
            println!(
                "⏭ SKIPPED: {} (requires RUN_EXPENSIVE_TESTS env var)",
                test_case.name
            );
            skipped += 1;
            continue;
        }

        print!("Testing: {:.<40}", test_case.name);

        let result = if test_case.name == "empty_partials_aggregation" {
            // Special case for empty partials test
            execute_empty_partials_test()
        } else if test_case.name == "wrong_message_verification_fails" {
            // Special case for wrong message test
            execute_wrong_message_test(&test_case.config)
        } else if test_case.name == "tampered_signature_fails" {
            // Special case for tampered signature test
            execute_tampered_signature_test(&test_case.config)
        } else if test_case.name == "tampered_partial_negates_threshold_fails" {
            // Special case for tampered partial test
            execute_tampered_partial_fails_test(&test_case.config)
        } else if test_case.name == "tampered_partial_maintains_threshold_success" {
            // Special case for tampered partial test
            execute_tampered_partial_succeeds_test(&test_case.config)
        } else if test_case.name == "invalid_domain_error_details" {
            // Special case for invalid domain test
            execute_invalid_domain_test()
        } else {
            // Normal test execution
            tracker.measure(test_case.name, || execute_test_case(&test_case))
        };
        match result {
            Ok(_) => println!("\x1b[32m✓ PASSED\x1b[0m"),
            Err(e) => {
                println!("\x1b[31m✗ FAILED: {}\x1b[0m", e);
                failed += 1;
            }
        }
    }

    // Print summary
    println!(
        "\n\x1b[1mTest Summary:\x1b[0m \x1b[32m{}/{} passed\x1b[0m, \x1b[31m{} failed\x1b[0m, \x1b[33m{} skipped\x1b[0m",
        total - failed - skipped,
        total,
        failed,
        skipped
    );

    // Print performance stats if requested
    if std::env::var("PRINT_PERFORMANCE_STATS").is_ok() {
        println!("\nPerformance Statistics:");
        tracker.print_stats();
    }

    // Fail the test if any cases failed
    assert_eq!(failed, 0, "{} test cases failed", failed);
}

// === Test Execution Functions ===

/// Execute a standard test case
fn execute_test_case(test_case: &TestCase) -> Result<(), String> {
    TestCaseBuilder::new()
        .domain_power(test_case.config.domain_power)
        .weights(test_case.config.weight_strategy.clone())
        .signers(test_case.config.signers.clone())
        .message(test_case.config.message.clone())
        .threshold(test_case.config.threshold_strategy)
        .expect(test_case.expected)
        .run()
}

/// Special execution for empty partials test
fn execute_empty_partials_test() -> Result<(), String> {
    // Create environment directly to test empty partials
    let mut env = TestEnvironment::new(2, WeightStrategy::Uniform(1)) // 2^2 = 4
        .map_err(|e| format!("Failed to create environment: {:?}", e))?;

    env.complete_setup()
        .map_err(|e| format!("Setup failed: {:?}", e))?;

    // Empty partials vector
    let partials = Vec::new();
    let threshold = crate::F::one();

    // Should fail with threshold not met
    let result = env.aggregate(threshold, &partials, b"empty partials test");
    match result {
        Err(HintsError::ThresholdNotMet) => Ok(()),
        other => Err(format!("Expected ThresholdNotMet error, got {:?}", other)),
    }
}

/// Special execution for wrong message test
fn execute_wrong_message_test(config: &TestConfig) -> Result<(), String> {
    // Create environment
    let mut env = TestEnvironment::new(config.domain_power, config.weight_strategy.clone())
        .map_err(|e| format!("Failed to create environment: {:?}", e))?;

    env.complete_setup()
        .map_err(|e| format!("Setup failed: {:?}", e))?;

    // Generate partial signatures for original message
    let original_msg = &config.message;
    let partials = env.generate_partial_signatures(&config.signers, original_msg);

    // Calculate threshold
    let threshold = env.sum_weights(&config.signers);

    // Aggregate signature for original message
    let signature = env
        .aggregate(threshold, &partials, original_msg)
        .map_err(|e| format!("Aggregation failed: {:?}", e))?;

    // Create modified message
    let mut modified_msg = original_msg.clone();
    if !modified_msg.is_empty() {
        modified_msg[0] ^= 1; // Flip a bit
    } else {
        modified_msg = vec![1]; // Add a byte if empty
    }

    // Verify with modified message - should fail
    match env.verify(&signature, &modified_msg) {
        Err(_) => Ok(()), // Expected failure
        Ok(()) => Err("Signature verified with wrong message!".to_string()),
    }
}

/// Special execution for tampered signature test
fn execute_tampered_signature_test(config: &TestConfig) -> Result<(), String> {
    // Create environment
    let mut env = TestEnvironment::new(config.domain_power, config.weight_strategy.clone())
        .map_err(|e| format!("Failed to create environment: {:?}", e))?;

    env.complete_setup()
        .map_err(|e| format!("Setup failed: {:?}", e))?;

    let msg = b"signature tampering test";

    // Generate partial signatures
    let partials = env.generate_partial_signatures(&config.signers, msg);

    // Calculate threshold
    let threshold = env.sum_weights(&config.signers);

    // Aggregate signature
    let mut signature = env
        .aggregate(threshold, &partials, msg)
        .map_err(|e| format!("Aggregation failed: {:?}", e))?;

    // Verify the original signature works
    match env.verify(&signature, msg) {
        Ok(()) => {}
        _ => return Err("Original signature failed to verify".to_string()),
    }

    // Tamper with the signature (modify the threshold)
    signature.threshold += crate::F::one();

    // Verify with tampered signature - should fail
    match env.verify(&signature, msg) {
        Err(_) => Ok(()), // Expected failure
        Ok(()) => Err("Tampered signature verified!".to_string()),
    }
}

/// Special execution for tampered signature test
fn execute_tampered_partial_fails_test(config: &TestConfig) -> Result<(), String> {
    // Create environment
    let mut env = TestEnvironment::new(config.domain_power, config.weight_strategy.clone())
        .map_err(|e| format!("Failed to create environment: {:?}", e))?;

    env.complete_setup()
        .map_err(|e| format!("Setup failed: {:?}", e))?;

    let msg = b"signature tampering test";

    // Generate partial signatures
    let mut partials = env.generate_partial_signatures(&config.signers, msg);

    // invalidate two of the partials

    partials[0].1 .0 = crate::G2::rand(&mut ark_std::test_rng());
    partials[1].1 .0 = crate::G2::rand(&mut ark_std::test_rng());

    // Calculate threshold
    let threshold = env.sum_weights(&config.signers);

    // Aggregate signature
    let signature = env.aggregate(threshold, &partials, msg);

    if signature.is_ok() {
        return Err("Signature should have failed to generate".to_string());
    }

    // not checking validity should succeed
    env.aggregate_unchecked(threshold, &partials, msg)
        .map(|_| ())
        .map_err(|e| format!("Uncheckced aggregation failed: {:?}", e))
}

/// Special execution for tampered signature test
fn execute_tampered_partial_succeeds_test(config: &TestConfig) -> Result<(), String> {
    // Create environment
    let mut env = TestEnvironment::new(config.domain_power, config.weight_strategy.clone())
        .map_err(|e| format!("Failed to create environment: {:?}", e))?;

    env.complete_setup()
        .map_err(|e| format!("Setup failed: {:?}", e))?;

    let msg = b"signature tampering test";

    // Generate partial signatures
    let mut partials = env.generate_partial_signatures(&config.signers, msg);

    // invalidate only one of the partials

    partials[0].1 .0 = crate::G2::rand(&mut ark_std::test_rng());

    // Aggregate signature
    env.aggregate(2.into(), &partials, msg)
        .map_err(|e| format!("Aggregation failed: {:?}", e))
        .map(|_| ())
}
/// Special execution for invalid domain test
fn execute_invalid_domain_test() -> Result<(), String> {
    let mut rng = seeded_rng();
    let domain_max = 3; // Not a power of 2

    // Attempt to create GlobalData with invalid domain
    let kzg_result = crate::KZG::setup(domain_max, &mut rng);

    if kzg_result.is_ok() {
        return Err("KZG setup with invalid domain should have failed".to_string());
    }

    // Verify error details
    let error_message = format!("{:?}", kzg_result.unwrap_err());
    if !error_message.contains("size") && !error_message.contains("power") {
        return Err(format!(
            "Error message should mention domain size issue, got: {}",
            error_message
        ));
    }

    Ok(())
}
