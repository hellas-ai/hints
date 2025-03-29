use hints::snark::{finish_setup, hintgen, SetupResult, F, G1, G2};
use hints::{HintsError, SecretKey};

use ark_ff::{One, UniformRand};
use ark_std::rand::Rng;

#[path = "test_helpers.rs"]
mod test_helpers;
use test_helpers::*;

#[test]
fn test_tampered_signature_fails_verification() {
    let mut rng = seeded_rng();
    let domain_max = 4;
    let n_participants = domain_max - 1;
    let msg = b"tampering test";

    // Setup
    let mut fixture =
        TestFixture::new(domain_max, n_participants, &mut rng).expect("Test setup failed");
    fixture.complete_setup().expect("Complete setup failed");

    // Generate a valid signature
    let partials = fixture.generate_signatures(&[0, 1, 2], msg);
    let threshold = F::one();
    let mut signature = fixture
        .aggregate(threshold, &partials, msg)
        .expect("Aggregation failed");

    // Make a copy of the original signature for comparison
    let original_signature = signature.clone();

    // Tamper with the signature (different ways to tamper)
    match rng.gen_range(0..3) {
        0 => {
            // Tamper with aggregated weight
            signature.proof.agg_weight = signature.proof.agg_weight + F::one();
            println!("Tampered with aggregated weight");
        }
        1 => {
            // Tamper with the proof
            signature.proof.w_of_r = F::rand(&mut rng);
            println!("Tampered with proof evaluation point");
        }
        _ => {
            // Tamper with the BLS signature itself
            signature.agg_sig_prime = G2::rand(&mut rng);
            println!("Tampered with BLS signature component");
        }
    }

    // Verification should fail
    let result = fixture.verify(&signature, msg);
    assert!(
        result.is_err() || result.unwrap() == false,
        "Verification of tampered signature should fail"
    );

    // Original signature should still verify
    assert!(
        fixture.verify(&original_signature, msg).unwrap_or(false),
        "Original untampered signature should still verify"
    );
}

#[test]
fn test_out_of_bounds_participant_ignored() {
    let mut rng = seeded_rng();
    let domain_max = 4;
    let n_participants = domain_max - 1;
    let msg = b"out of bounds test";

    // Setup
    let mut fixture =
        TestFixture::new(domain_max, n_participants, &mut rng).expect("Test setup failed");
    fixture.complete_setup().expect("Complete setup failed");

    // Generate valid partials
    let valid_partials = fixture.generate_signatures(&[0, 1], msg);

    // Create an out-of-bounds partial
    let invalid_sk = SecretKey::random(&mut rng);
    let out_of_bounds_partial = (n_participants, invalid_sk.sign(msg)); // Invalid index

    // Combine valid and invalid partials
    let mut all_partials = valid_partials.clone();
    all_partials.push(out_of_bounds_partial);

    // Threshold based on valid signers only
    let threshold = fixture.sum_weights(&[0, 1]);

    // Aggregate - should succeed by ignoring out-of-bounds partial
    let signature = fixture
        .aggregate(threshold, &all_partials, msg)
        .expect("Aggregation should succeed, ignoring out-of-bounds partial");

    // Verify
    assert!(fixture
        .verify(&signature, msg)
        .expect("Verification failed"));

    // Check that signature is identical to one with only valid partials
    let valid_only_sig = fixture
        .aggregate(threshold, &valid_partials, msg)
        .expect("Aggregation with valid partials failed");

    // Compare signatures (format as strings for easier comparison)
    assert_eq!(
        format!("{:?}", signature),
        format!("{:?}", valid_only_sig),
        "Signatures should be identical when invalid partials are ignored"
    );
}

#[test]
fn test_duplicate_partial_signatures() {
    let mut rng = seeded_rng();
    let domain_max = 4;
    let n_participants = domain_max - 1;
    let msg = b"duplicate partials test";

    // Setup
    let mut fixture =
        TestFixture::new(domain_max, n_participants, &mut rng).expect("Test setup failed");
    fixture.complete_setup().expect("Complete setup failed");

    // Generate valid partials
    let mut partials = fixture.generate_signatures(&[0, 1], msg);

    // Duplicate participant 0's signature
    let duplicate = partials[0].clone();
    partials.push(duplicate);

    // Threshold based on weights of 0 and 1
    let threshold = fixture.sum_weights(&[0, 1]);

    // Aggregate - implementation should deduplicate or use first occurrence
    let signature = fixture
        .aggregate(threshold, &partials, msg)
        .expect("Aggregation with duplicate partials failed");

    // Verify
    assert!(fixture
        .verify(&signature, msg)
        .expect("Verification failed"));

    // Should match signature created with only unique partials
    let unique_partials = fixture.generate_signatures(&[0, 1], msg);
    let unique_sig = fixture
        .aggregate(threshold, &unique_partials, msg)
        .expect("Aggregation with unique partials failed");

    // Check that duplicates didn't affect the result
    assert_eq!(
        format!("{:?}", signature.proof.agg_weight),
        format!("{:?}", unique_sig.proof.agg_weight),
        "Duplicate partials should not affect the aggregated weight"
    );
}

#[test]
fn test_security_properties() {
    let mut rng = seeded_rng();
    let domain_max = 8;
    let n_participants = domain_max - 1;
    let msg1 = b"first message";
    let msg2 = b"second message";

    // Setup
    let mut fixture =
        TestFixture::new(domain_max, n_participants, &mut rng).expect("Test setup failed");
    fixture.complete_setup().expect("Complete setup failed");

    // 1. Unforgeability: Cannot create valid signature without enough participants
    let high_threshold = F::from(10000u32); // Higher than sum of all weights
    let insufficient_partials = fixture.generate_signatures(&[0], msg1);
    let result = fixture.aggregate(high_threshold, &insufficient_partials, msg1);
    assert!(matches!(result, Err(HintsError::ThresholdNotMet)));

    // 2. Non-malleability: Cannot convert signature for one message to another
    let sufficient_partials = fixture.generate_signatures(&[0, 1, 2], msg1);
    let threshold = fixture.sum_weights(&[0, 1, 2]);
    let signature = fixture
        .aggregate(threshold, &sufficient_partials, msg1)
        .expect("Aggregation failed");

    // Attempt to verify signature against different message
    let result = fixture.verify(&signature, msg2);
    assert!(
        result.is_err() || result.unwrap() == false,
        "Signature should not verify for different message"
    );
}

#[test]
fn test_invalid_hint_handling() {
    let mut rng = seeded_rng();
    let domain_max = 4;
    let n_participants = domain_max - 1;
    let msg = b"invalid hint test";

    // Setup initial environment
    let (gd, sks, pks, mut hints, weights) =
        setup_test_env(domain_max, n_participants, &mut rng).expect("Test setup failed");

    // Create an invalid hint for participant 1
    let invalid_sk = SecretKey::random(&mut rng);
    let invalid_hint = hintgen(&gd, &invalid_sk, domain_max, 1).expect("Hint generation failed");
    hints[1] = invalid_hint; // Replace valid hint with invalid one

    // Run finish_setup - should succeed but report the invalid hint
    let setup_result = finish_setup(&gd, domain_max, pks.clone(), &hints, weights.clone());
    assert!(
        setup_result.is_ok(),
        "Setup should succeed with invalid hints"
    );

    let SetupResult {
        agg_key,
        vk,
        party_errors,
    } = setup_result.unwrap();

    // Check that the error for participant 1 was reported
    assert!(
        !party_errors.is_empty(),
        "Should have reported party errors"
    );
    assert!(
        party_errors.iter().any(|(idx, _)| *idx == 1),
        "Should have reported error for party 1"
    );

    // Try to aggregate signatures - include participant 1
    let all_partials = generate_partials(&sks, msg, &[0, 1, 2]);

    // Set threshold low enough that 0 and 2 would pass
    let threshold = weights[0] + weights[2];

    // Aggregate - should succeed, automatically ignoring participant 1 due to failed hint
    let signature = agg_key
        .aggregate(&gd, threshold, &all_partials, weights.clone(), msg)
        .expect("Aggregation should succeed, ignoring party with failed hint");

    // Verify - should succeed
    let verify_result = signature.verify(&gd, &vk, msg);
    assert!(
        verify_result.is_ok() && *verify_result.as_ref().unwrap(),
        "Verification should succeed: {:?}",
        verify_result
    );

    // Verify that the proof weight only includes 0 and 2
    assert_eq!(
        signature.proof.agg_weight,
        weights[0] + weights[2],
        "Aggregated weight should only include valid parties"
    );
}
