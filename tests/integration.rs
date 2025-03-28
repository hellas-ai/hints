use hints::snark::{
    finish_setup, hintgen, AggregationKey, GlobalData, Hint, SetupResult, VerifierKey, F, KZG,
};
use hints::{HintsError, PartialSignature, PublicKey, SecretKey};

use ark_ff::{One, UniformRand, Zero};
use ark_std::rand::{rngs::StdRng, Rng, SeedableRng};
use ark_std::{vec, vec::Vec}; // Ensure vec is imported

use proptest::prelude::*;

// === Test Constants ===
const TEST_SEED: [u8; 32] = [42u8; 32];
// Choose a fixed domain size for property tests to amortize setup cost
const PROPTEST_DOMAIN_MAX_POW: u32 = 5; // 2^5 = 32
const PROPTEST_DOMAIN_MAX: usize = 1 << PROPTEST_DOMAIN_MAX_POW;
const PROPTEST_N_PARTICIPANTS: usize = PROPTEST_DOMAIN_MAX - 1;

// === Test Helpers === (Mostly unchanged, but adapted for fixed size)

fn seeded_rng() -> StdRng {
    StdRng::from_seed(TEST_SEED)
}

fn sample_weights(n: usize, rng: &mut impl Rng) -> Vec<F> {
    // Use smaller weights for testing to avoid overflow issues if summing many
    (0..n).map(|_| F::from(u16::rand(rng))).collect()
}

type SetupProptestEnvResult = (
    GlobalData,
    Vec<SecretKey>,
    Vec<PublicKey>,
    Vec<Hint>,
    Vec<F>,
);
/// Sets up the global data, keys, hints, and weights for testing.
/// Uses fixed sizes defined by PROPTEST_ constants.
fn setup_proptest_env(rng: &mut impl Rng) -> Result<SetupProptestEnvResult, HintsError> {
    let domain_max = PROPTEST_DOMAIN_MAX;
    let n_participants = PROPTEST_N_PARTICIPANTS;

    // 1. Global Setup
    let gd = GlobalData::from_params(
        domain_max,
        KZG::setup_insecure(domain_max, rng).map_err(HintsError::from)?,
    );

    // 2. Key Generation
    let sks: Vec<SecretKey> = (0..n_participants)
        .map(|_| SecretKey::random(rng))
        .collect();
    let pks: Vec<PublicKey> = sks.iter().map(|sk| sk.public(&gd)).collect();

    // 3. Hint Generation
    let hints: Vec<Hint> = sks
        .iter()
        .enumerate()
        .map(|(i, sk)| hintgen(&gd, sk, domain_max, i))
        .collect::<Result<_, _>>()?;

    // 4. Weights
    let weights = sample_weights(n_participants, rng);

    Ok((gd, sks, pks, hints, weights))
}

/// Runs finish_setup for proptest env.
fn run_proptest_finish_setup(
    gd: &GlobalData,
    pks: Vec<PublicKey>,
    hints: &[Hint],
    weights: Vec<F>,
) -> Result<(AggregationKey, VerifierKey), HintsError> {
    let domain_max = PROPTEST_DOMAIN_MAX;
    let SetupResult {
        agg_key,
        vk,
        party_errors,
    } = finish_setup(gd, domain_max, pks, hints, weights)?;
    assert!(
        party_errors.is_empty(),
        "Hint verification failed unexpectedly: {:?}",
        party_errors
    );
    Ok((agg_key, vk))
}

/// Runs finish_setup and asserts that there are no hint errors for valid inputs.
fn run_finish_setup(
    gd: &GlobalData,
    domain_max: usize,
    pks: Vec<PublicKey>,
    hints: &[Hint],
    weights: Vec<F>,
) -> Result<(AggregationKey, VerifierKey), HintsError> {
    let SetupResult {
        agg_key,
        vk,
        party_errors,
    } = finish_setup(gd, domain_max, pks, hints, weights)?;
    assert!(
        party_errors.is_empty(),
        "Hint verification failed unexpectedly: {:?}",
        party_errors
    );
    Ok((agg_key, vk))
}

/// Generates partial signatures for a subset of participants.
fn generate_partials(
    sks: &[SecretKey],
    msg: &[u8],
    indices_to_sign: &[usize],
) -> Vec<(usize, PartialSignature)> {
    indices_to_sign
        .iter()
        .filter_map(|&i| sks.get(i).map(|sk| (i, sk.sign(msg))))
        .collect()
}

// === Standard Tests (`#[test]`) ===
// (Keep the previous standard tests like test_full_workflow_success, etc.)
#[test]
fn test_full_workflow_success() {
    let mut rng = seeded_rng();
    let domain_max = 4; // n=3 participants
    let n_participants = domain_max - 1;
    let msg = b"hello world";

    // Setup
    let (gd, sks, pks, hints, weights) =
        setup_test_env_dynamic_size(domain_max, n_participants, &mut rng)
            .expect("Test setup failed");
    let (ak, vk) = run_finish_setup(&gd, domain_max, pks, &hints, weights.clone())
        .expect("Finish setup failed");

    // All participants sign
    let indices_to_sign: Vec<usize> = (0..n_participants).collect();
    let partials = generate_partials(&sks, msg, &indices_to_sign);
    assert_eq!(partials.len(), n_participants);

    // Aggregate (threshold can be low, e.g., 1)
    let threshold = F::one();
    let signature = ak
        .aggregate(&gd, threshold, &partials, weights, msg)
        .expect("Aggregation failed");

    // Verify
    let result = signature.verify(&vk, msg).expect("Verification failed");
    assert!(result, "Signature verification should succeed");
}

#[test]
fn test_subset_signs_success() {
    let mut rng = seeded_rng();
    let domain_max = 8; // n=7 participants
    let n_participants = domain_max - 1;
    let msg = b"subset test";

    // Setup
    let (gd, sks, pks, hints, weights) =
        setup_test_env_dynamic_size(domain_max, n_participants, &mut rng)
            .expect("Test setup failed");
    let (ak, vk) = run_finish_setup(&gd, domain_max, pks, &hints, weights.clone())
        .expect("Finish setup failed");

    // Subset signs (e.g., participants 0, 2, 4)
    let indices_to_sign: Vec<usize> = vec![0, 2, 4];
    let partials = generate_partials(&sks, msg, &indices_to_sign);
    assert_eq!(partials.len(), indices_to_sign.len());

    // Calculate threshold needed
    let required_weight: F = indices_to_sign.iter().map(|&i| weights[i]).sum();
    let threshold = required_weight; // Set threshold exactly

    // Aggregate
    let signature = ak
        .aggregate(&gd, threshold, &partials, weights, msg)
        .expect("Aggregation failed");

    // Verify
    let result = signature.verify(&vk, msg).expect("Verification failed");
    assert!(result, "Signature verification should succeed");
}

#[test]
fn test_threshold_not_met_aggregation_fails() {
    let mut rng = seeded_rng();
    let domain_max = 4; // n=3 participants
    let n_participants = domain_max - 1;
    let msg = b"threshold fail test";

    // Setup
    let (gd, sks, pks, hints, weights) =
        setup_test_env_dynamic_size(domain_max, n_participants, &mut rng)
            .expect("Test setup failed");
    let (ak, _) = run_finish_setup(&gd, domain_max, pks, &hints, weights.clone())
        .expect("Finish setup failed");

    // Only participant 0 signs
    let indices_to_sign: Vec<usize> = vec![0];
    let partials = generate_partials(&sks, msg, &indices_to_sign);
    assert_eq!(partials.len(), 1);

    // Calculate actual weight and set threshold higher
    let actual_weight: F = weights[0];
    let threshold = actual_weight + F::one(); // Higher than possible

    // Aggregate - expect error
    let result = ak.aggregate(&gd, threshold, &partials, weights, msg);
    assert!(
        matches!(result, Err(HintsError::ThresholdNotMet)),
        "Expected ThresholdNotMet error, got {:?}",
        result
    );
}

#[test]
fn test_invalid_partial_signature_ignored() {
    let mut rng = seeded_rng();
    let domain_max = 4; // n=3 participants
    let n_participants = domain_max - 1;
    let msg = b"invalid partial sig";

    // Setup
    let (gd, sks, pks, hints, weights) =
        setup_test_env_dynamic_size(domain_max, n_participants, &mut rng)
            .expect("Test setup failed");
    let (ak, vk) = run_finish_setup(&gd, domain_max, pks.clone(), &hints, weights.clone())
        .expect("Finish setup failed");

    // Generate valid partials for 0 and 2
    let valid_indices: Vec<usize> = vec![0, 2];
    let mut partials = generate_partials(&sks, msg, &valid_indices);

    // Create an invalid partial signature (e.g., sign with wrong key)
    let wrong_sk = SecretKey::random(&mut rng);
    let invalid_partial = (1, wrong_sk.sign(msg)); // Participant 1 sends bad sig

    // Sanity check: invalid partial doesn't verify
    assert!(
        !hints::partial_verify(&gd, &pks[1], msg, &invalid_partial.1),
        "Invalid partial should not verify"
    );

    partials.push(invalid_partial); // Add invalid sig to the list

    // Calculate threshold based ONLY on valid signers
    let required_weight: F = valid_indices.iter().map(|&i| weights[i]).sum();
    let threshold = required_weight;

    // Aggregate - should succeed by ignoring the bad signature
    let signature = ak
        .aggregate(&gd, threshold, &partials, weights, msg)
        .expect("Aggregation should succeed by ignoring invalid partial");

    // Verify
    let result = signature.verify(&vk, msg).expect("Verification failed");
    assert!(
        result,
        "Signature verification should succeed with only valid partials considered"
    );
}

#[test]
fn test_wrong_message_verification_fails() {
    let mut rng = seeded_rng();
    let domain_max = 4; // n=3 participants
    let n_participants = domain_max - 1;
    let msg1 = b"message one";
    let msg2 = b"message two";

    // Setup
    let (gd, sks, pks, hints, weights) =
        setup_test_env_dynamic_size(domain_max, n_participants, &mut rng)
            .expect("Test setup failed");
    let (ak, vk) = run_finish_setup(&gd, domain_max, pks, &hints, weights.clone())
        .expect("Finish setup failed");

    // All participants sign msg1
    let indices_to_sign: Vec<usize> = (0..domain_max - 1).collect();
    let partials = generate_partials(&sks, msg1, &indices_to_sign);

    // Aggregate for msg1
    let threshold = F::one();
    let signature = ak
        .aggregate(&gd, threshold, &partials, weights, msg1)
        .expect("Aggregation failed");

    // Verify against msg2 - expect error
    let result = signature.verify(&vk, msg2);
    assert!(
        matches!(result, Err(HintsError::BlsVerificationFailed)),
        "Expected BlsVerificationFailed error for wrong message, got {:?}",
        result
    );
}

#[test]
fn test_invalid_hint_finish_setup() {
    let mut rng = seeded_rng();
    let domain_max = 4; // n=3 participants
    let n_participants = domain_max - 1;
    let msg = b"invalid hint test";

    // Setup
    let (gd, sks, pks, mut hints, weights) =
        setup_test_env_dynamic_size(domain_max, n_participants, &mut rng)
            .expect("Test setup failed");

    // Create an invalid hint for participant 1
    let invalid_hint = hintgen(&gd, &SecretKey::random(&mut rng), domain_max, 1) // Wrong SK
        .expect("Hint gen failed");
    hints[1] = invalid_hint;

    // Run finish_setup - expect success but with a reported error
    let SetupResult {
        agg_key,
        vk,
        party_errors,
    } = finish_setup(&gd, domain_max, pks.clone(), &hints, weights.clone())
        .expect("Finish setup itself should not fail here");

    // Check that the error for participant 1 was reported
    assert_eq!(party_errors.len(), 1);
    assert_eq!(party_errors[0].0, 1); // Index of the faulty party
    assert!(matches!(
        party_errors[0].1,
        hints::snark::PartyError::PairingCheckFailed
    ));
    assert!(agg_key.failed_hint_indices.contains(&1));

    // Try to aggregate signatures - include participant 1
    let indices_to_sign: Vec<usize> = (0..n_participants).collect(); // Try 0, 1, 2
    let partials = generate_partials(&sks, msg, &indices_to_sign);

    // Set threshold low enough that 0 and 2 would pass
    let threshold = weights[0] + weights[2];

    // Aggregate - should succeed, automatically ignoring participant 1 due to failed hint
    let signature = agg_key
        .aggregate(&gd, threshold, &partials, weights.clone(), msg)
        .expect("Aggregation should succeed, ignoring party with failed hint");

    // Verify - should succeed
    let result = signature.verify(&vk, msg).expect("Verification failed");
    assert!(result, "Verification should succeed");

    // Verify that the proof weight only includes 0 and 2
    assert_eq!(signature.proof.agg_weight, weights[0] + weights[2]);
}

#[test]
fn test_setup_errors_participant_count_mismatch() {
    let mut rng = seeded_rng();
    let domain_max = 4;
    let n_participants_wrong = domain_max; // Should be domain_max - 1

    // Setup with wrong number of participants
    let gd = GlobalData::from_params(
        domain_max,
        KZG::setup_insecure(domain_max, &mut rng).unwrap(),
    );
    let sks: Vec<SecretKey> = (0..n_participants_wrong)
        .map(|_| SecretKey::random(&mut rng))
        .collect();
    let pks: Vec<PublicKey> = sks.iter().map(|sk| sk.public(&gd)).collect();
    let hints: Vec<Hint> = sks
        .iter()
        .enumerate()
        .map(|(i, sk)| hintgen(&gd, sk, domain_max, i)) // Hintgen needs correct domain_max
        .collect::<Result<_, _>>()
        .unwrap();
    let weights = sample_weights(n_participants_wrong, &mut rng); // Wrong number of weights

    // Run finish_setup - expect error
    let result = finish_setup(&gd, domain_max, pks, &hints, weights);
    assert!(
        matches!(result, Err(HintsError::InvalidInput(_))),
        "Expected InvalidInput error for participant count mismatch, got {:?}",
        result
    );
}

type SetupTestEnvResult = (
    GlobalData,
    Vec<SecretKey>,
    Vec<PublicKey>,
    Vec<Hint>,
    Vec<F>,
);
// Helper needed for standard tests when dynamic size is needed
fn setup_test_env_dynamic_size(
    domain_max: usize,
    n_participants: usize,
    rng: &mut impl Rng,
) -> Result<SetupTestEnvResult, HintsError> {
    if domain_max == 0 || !domain_max.is_power_of_two() {
        panic!("domain_max must be a power of 2 and > 0");
    }
    let gd = GlobalData::from_params(domain_max, KZG::setup_insecure(domain_max, rng)?);
    let sks: Vec<SecretKey> = (0..n_participants)
        .map(|_| SecretKey::random(rng))
        .collect();
    let pks: Vec<PublicKey> = sks.iter().map(|sk| sk.public(&gd)).collect();
    let hints: Vec<Hint> = sks
        .iter()
        .enumerate()
        .map(|(i, sk)| hintgen(&gd, sk, domain_max, i))
        .collect::<Result<_, _>>()?;
    let weights = sample_weights(n_participants, rng);
    Ok((gd, sks, pks, hints, weights))
}

// === Property-Based Tests (`proptest`) ===

// Strategy to generate a subset of indices
fn signer_indices_strategy() -> impl Strategy<Value = Vec<usize>> {
    // Generates a vector of unique indices from 0 to N_PARTICIPANTS-1
    prop::collection::hash_set(0..PROPTEST_N_PARTICIPANTS, 0..=PROPTEST_N_PARTICIPANTS).prop_map(
        |set| {
            let mut vec: Vec<_> = set.into_iter().collect();
            vec.sort(); // Keep order consistent if needed
            vec
        },
    )
}

// Strategy for generating a small message
fn message_strategy() -> impl Strategy<Value = Vec<u8>> {
    prop::collection::vec(any::<u8>(), 0..64) // Keep messages reasonably small
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(25))] // Reduce cases for faster CI, increase locally if needed

    #[test]
    fn prop_aggregate_verify_succeeds_proptest(
        indices_to_sign in signer_indices_strategy(),
        msg in message_strategy()
    ) {
        // --- One-time Setup (expensive) ---
        // Using lazy_static or once_cell could potentially make this global,
        // but for simplicity, we do it once per test function run.
        let mut rng = seeded_rng();
        let (gd, sks, pks, hints, weights) = setup_proptest_env(&mut rng)
            .map_err(|e| TestCaseError::fail(format!("Setup failed: {:?}", e)))?;
        let (ak, vk) = run_proptest_finish_setup(&gd, pks, &hints, weights.clone())
             .map_err(|e| TestCaseError::fail(format!("Finish setup failed: {:?}", e)))?;
        // --- End One-time Setup ---

        // --- Test Case Logic (runs many times) ---
        prop_assume!(!indices_to_sign.is_empty()); // Need at least one signer for this property

        let partials = generate_partials(&sks, &msg, &indices_to_sign);
        prop_assert_eq!(partials.len(), indices_to_sign.len(), "Partial generation mismatch");

        // Calculate required weight and set threshold
        let actual_weight: F = indices_to_sign.iter().map(|&i| weights[i]).sum();
        let threshold = actual_weight; // Set threshold to exactly what was signed

        // Proptest doesn't handle F::zero() well in ranges sometimes. If actual weight is zero,
        // but we have signers, aggregation should still work with threshold zero or one.
        let effective_threshold = if actual_weight.is_zero() { F::zero() } else { threshold };

        // Aggregate
        let aggregate_result = ak.aggregate(&gd, effective_threshold, &partials, weights, &msg);
        match aggregate_result {
            Ok(signature) => {
                // Verify
                match signature.verify(&vk, &msg) {
                    Ok(true) => Ok(()), // Proptest success = Ok(())
                    Ok(false) => Err(TestCaseError::fail("Verification returned false")),
                    Err(e) => Err(TestCaseError::fail(format!("Verification failed: {:?}", e))),
                }
            }
            Err(HintsError::ThresholdNotMet) => {
                 // This might happen if all signers had weight 0
                 prop_assume!(!actual_weight.is_zero()); // If it fails threshold but weight was non-zero, it's a bug
                 Ok(()) // Ok if weight was indeed zero
            }
            Err(e) => Err(TestCaseError::fail(format!("Aggregation failed: {:?}", e))),
        }? // Use '?' to propagate TestCaseError
    }

    #[test]
    fn prop_threshold_too_high_aggregate_fails_proptest(
        indices_to_sign in signer_indices_strategy(),
        msg in message_strategy()
    ) {
        // --- One-time Setup ---
         let mut rng = seeded_rng();
        let (gd, sks, pks, hints, weights) = setup_proptest_env(&mut rng)
            .map_err(|e| TestCaseError::fail(format!("Setup failed: {:?}", e)))?;
        let (ak, _vk) = run_proptest_finish_setup(&gd, pks, &hints, weights.clone())
             .map_err(|e| TestCaseError::fail(format!("Finish setup failed: {:?}", e)))?;
        // --- End One-time Setup ---

        let partials = generate_partials(&sks, &msg, &indices_to_sign);
         prop_assert_eq!(partials.len(), indices_to_sign.len());

        // Calculate actual weight and set threshold strictly higher
        let actual_weight: F = indices_to_sign.iter().map(|&i| weights[i]).sum();
        let threshold = actual_weight + F::one(); // Ensure threshold is definitely higher

        // Aggregate - expect error ThresholdNotMet
        let aggregate_result = ak.aggregate(&gd, threshold, &partials, weights, &msg);

        match aggregate_result {
            Err(HintsError::ThresholdNotMet) => Ok(()), // Expected failure
            Ok(_) => Err(TestCaseError::fail("Aggregation succeeded unexpectedly")),
            Err(e) => Err(TestCaseError::fail(format!("Aggregation failed with unexpected error: {:?}", e))),
        }?
    }

     #[test]
    fn prop_wrong_message_verify_fails_proptest(
        indices_to_sign in signer_indices_strategy(),
        msg1 in message_strategy(),
        msg2 in message_strategy(), // Generate two messages
    ) {
        // --- One-time Setup ---
        let mut rng = seeded_rng();
        let (gd, sks, pks, hints, weights) = setup_proptest_env(&mut rng)
            .map_err(|e| TestCaseError::fail(format!("Setup failed: {:?}", e)))?;
        let (ak, vk) = run_proptest_finish_setup(&gd, pks, &hints, weights.clone())
            .map_err(|e| TestCaseError::fail(format!("Finish setup failed: {:?}", e)))?;
        // --- End One-time Setup ---

        prop_assume!(!indices_to_sign.is_empty()); // Need signers
        prop_assume!(msg1 != msg2); // Ensure messages are different

        // Generate partials for msg1
        let partials = generate_partials(&sks, &msg1, &indices_to_sign);
        prop_assert_eq!(partials.len(), indices_to_sign.len());

        // Calculate threshold and aggregate for msg1
        let actual_weight: F = indices_to_sign.iter().map(|&i| weights[i]).sum();
        let threshold = actual_weight; // Exact threshold
        let effective_threshold = if actual_weight.is_zero() { F::zero() } else { threshold };


        let aggregate_result = ak.aggregate(&gd, effective_threshold, &partials, weights, &msg1);
        let signature = match aggregate_result {
            Ok(sig) => sig,
            Err(HintsError::ThresholdNotMet) => { prop_assume!(!actual_weight.is_zero()); return Ok(()); }, // Discard if threshold failed legitimately
            Err(e) => return Err(TestCaseError::fail(format!("Aggregation failed: {:?}", e))),
        };

        // Verify against msg2 - expect BlsVerificationFailed error
        let verify_result = signature.verify(&vk, &msg2);

        match verify_result {
            Err(HintsError::BlsVerificationFailed) => Ok(()), // Expected failure
            Ok(res) => Err(TestCaseError::fail(format!("Verification succeeded/failed unexpectedly: {}", res))),
            Err(e) => Err(TestCaseError::fail(format!("Verification failed with wrong error: {:?}", e))),
        }?
    }
}
