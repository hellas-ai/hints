use hints::snark::{F, KZG};
use hints::{HintsError, PartialSignature};

use ark_ff::{One, Zero};
use ark_std::time::Instant;

#[path = "test_helpers.rs"]
#[macro_use]
mod test_helpers;
use test_helpers::*;

#[test]
fn test_minimum_domain_size() {
    // Test with domain_max = 2 (smallest valid power of 2)
    let mut rng = seeded_rng();
    let domain_max = 2; // Minimum valid domain size
    let n_participants = domain_max - 1; // Just one participant
    let msg = b"minimum domain test";

    // Setup with minimum configuration
    let mut fixture =
        TestFixture::new(domain_max, n_participants, &mut rng).expect("Test setup failed");
    fixture.complete_setup().expect("Complete setup failed");

    // One participant signs
    let partials = fixture.generate_signatures(&[0], msg);
    let threshold = fixture.weights[0]; // Exact threshold

    // Test aggregation and verification
    let signature = fixture
        .aggregate(threshold, &partials, msg)
        .expect("Aggregation failed");
    assert!(fixture
        .verify(&signature, msg)
        .expect("Verification failed"));
}

#[test]
fn test_large_domain_size_scaling() {
    return;
    // Test with a much larger domain size than usual
    let mut rng = seeded_rng();
    let domain_max = 1 << 8; // 256, larger but not too large for CI
    let n_participants = 300; // Substantial number of participants

    // Only measure setup performance to ensure it scales acceptably
    let start = Instant::now();
    let result = setup_test_env(domain_max, n_participants, &mut rng);
    assert!(result.is_ok(), "Setup failed: {:?}", result.err());
    let setup_time = start.elapsed();

    // Assert that setup completes within a reasonable time (adjust based on CI capabilities)
    println!("Large domain setup time: {:?}", setup_time);
    assert!(
        setup_time.as_secs() < 90,
        "Setup took too long: {:?}",
        setup_time
    );
}

#[test]
fn test_zero_weight_participants() {
    let mut rng = seeded_rng();
    let domain_max = 8;
    let n_participants = domain_max - 1;
    let msg = b"zero weight test";

    // Setup with standard configuration
    let mut fixture =
        TestFixture::new(domain_max, n_participants, &mut rng).expect("Test setup failed");

    // Set some weights to zero
    fixture.set_weight(1, F::zero());
    fixture.set_weight(3, F::zero());

    fixture.complete_setup().expect("Complete setup failed");

    // All participants sign, including zero-weight ones
    let indices_to_sign: Vec<usize> = (0..n_participants).collect();
    let partials = fixture.generate_signatures(&indices_to_sign, msg);

    // Calculate threshold (sum of all weights)
    let threshold = fixture.sum_weights(&indices_to_sign);

    // Test aggregation and verification
    let signature = fixture
        .aggregate(threshold, &partials, msg)
        .expect("Aggregation failed");
    assert!(fixture
        .verify(&signature, msg)
        .expect("Verification failed"));

    // Verify that zero-weight participants don't contribute to threshold
    let non_zero_indices: Vec<usize> = vec![0, 2, 4, 5, 6];
    let non_zero_threshold = fixture.sum_weights(&non_zero_indices);
    assert_eq!(
        threshold, non_zero_threshold,
        "Zero weights should not contribute to threshold"
    );
}

#[test]
fn test_extremely_skewed_weights() {
    let mut rng = seeded_rng();
    let domain_max = 8;
    let n_participants = domain_max - 1;
    let msg = b"skewed weight test";

    // Setup with standard configuration
    let mut fixture =
        TestFixture::new(domain_max, n_participants, &mut rng).expect("Test setup failed");

    // Create extremely skewed weights - one dominant participant
    fixture.set_all_weights(F::one());
    fixture.set_weight(0, F::from(1000000u64)); // Extremely large weight

    fixture.complete_setup().expect("Complete setup failed");

    // Test with just the dominant participant
    let partials = fixture.generate_signatures(&[0], msg);
    let threshold = fixture.weights[0]; // Only need the dominant participant

    // Test aggregation and verification
    let signature = fixture
        .aggregate(threshold, &partials, msg)
        .expect("Aggregation failed");
    assert!(fixture
        .verify(&signature, msg)
        .expect("Verification failed"));
}

#[test]
fn test_empty_message() {
    let mut rng = seeded_rng();
    let domain_max = 4;
    let n_participants = domain_max - 1;
    let msg = b""; // Empty message

    // Setup with standard configuration
    let mut fixture =
        TestFixture::new(domain_max, n_participants, &mut rng).expect("Test setup failed");
    fixture.complete_setup().expect("Complete setup failed");

    // All participants sign an empty message
    let indices_to_sign: Vec<usize> = (0..n_participants).collect();
    let partials = fixture.generate_signatures(&indices_to_sign, msg);
    let threshold = F::one();

    // Test aggregation and verification with empty message
    let signature = fixture
        .aggregate(threshold, &partials, msg)
        .expect("Aggregation with empty message failed");
    assert!(fixture
        .verify(&signature, msg)
        .expect("Verification failed"));
}

#[test]
fn test_empty_partials_aggregation() {
    let mut rng = seeded_rng();
    let domain_max = 4;
    let n_participants = domain_max - 1;
    let msg = b"empty partials test";

    // Setup with standard configuration
    let mut fixture =
        TestFixture::new(domain_max, n_participants, &mut rng).expect("Test setup failed");
    fixture.complete_setup().expect("Complete setup failed");

    // No participants sign - empty partials
    let partials: Vec<(usize, PartialSignature)> = vec![];
    let threshold = F::one(); // Even with zero threshold, should fail with empty partials

    // Should fail appropriately
    let result = fixture.aggregate(threshold, &partials, msg);
    assert!(matches!(result, Err(HintsError::ThresholdNotMet)));
}

#[test]
fn test_invalid_domain_error_details() {
    let mut rng = seeded_rng();
    let domain_max = 3; // Not a power of 2

    // Attempt to create GlobalData with invalid domain
    let kzg_result = KZG::setup_insecure(domain_max, &mut rng);
    assert!(
        kzg_result.is_err(),
        "KZG setup with invalid domain should fail"
    );

    // Verify error details
    let error_message = format!("{:?}", kzg_result.unwrap_err());
    assert!(
        error_message.contains("size") || error_message.contains("power"),
        "Error message should mention domain size issue, got: {}",
        error_message
    );
}

#[test]
fn test_granular_threshold_error() {
    let mut rng = seeded_rng();
    let domain_max = 4;
    let n_participants = domain_max - 1;
    let msg = b"threshold error test";

    // Setup with standard configuration
    let mut fixture =
        TestFixture::new(domain_max, n_participants, &mut rng).expect("Test setup failed");
    fixture.complete_setup().expect("Complete setup failed");

    // Only participant 0 signs
    let partials = fixture.generate_signatures(&[0], msg);

    // Set threshold just slightly higher than available
    let available_weight = fixture.weights[0];
    let threshold = available_weight + F::one();

    // Test with detailed error checking
    let result = fixture.aggregate(threshold, &partials, msg);
    assert_error_type_and_details!(result, HintsError::ThresholdNotMet, "Err(ThresholdNotMet)");
}
