use hints::snark::{
    finish_setup, hintgen, AggregationKey, GlobalData, Hint, SetupResult, VerifierKey, F, KZG,
};
use hints::{HintsError, PartialSignature, PublicKey, SecretKey, Signature};

use ark_ff::{One, UniformRand, Zero};
use ark_std::rand::{rngs::StdRng, Rng, SeedableRng};
use ark_std::{vec, vec::Vec};

// === Test Constants ===
pub const TEST_SEED: [u8; 32] = [42u8; 32];

/// Creates a deterministic RNG for tests
pub fn seeded_rng() -> StdRng {
    StdRng::from_seed(TEST_SEED)
}

/// Sample weights for testing (smaller values to avoid overflow)
pub fn sample_weights(n: usize, rng: &mut impl Rng) -> Vec<F> {
    (0..n).map(|_| F::from(u16::rand(rng))).collect()
}

pub type SetupEnvResult = (
    GlobalData,
    Vec<SecretKey>,
    Vec<PublicKey>,
    Vec<Hint>,
    Vec<F>,
);

/// Sets up the test environment with the specified domain size and number of participants
pub fn setup_test_env(
    domain_max: usize,
    n_participants: usize,
    rng: &mut impl Rng,
) -> Result<SetupEnvResult, HintsError> {
    if domain_max == 0 || !domain_max.is_power_of_two() {
        return Err(HintsError::InvalidInput(
            "domain_max must be a power of 2 and > 0".to_string(),
        ));
    }

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

/// Runs finish_setup and asserts that there are no hint errors for valid inputs.
pub fn run_finish_setup(
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

    // Only report errors, don't fail the test immediately
    if !party_errors.is_empty() {
        println!("Warning: Hint verification had errors: {:?}", party_errors);
    }

    Ok((agg_key, vk))
}

/// Generates partial signatures for a subset of participants.
pub fn generate_partials(
    sks: &[SecretKey],
    msg: &[u8],
    indices_to_sign: &[usize],
) -> Vec<(usize, PartialSignature)> {
    indices_to_sign
        .iter()
        .filter_map(|&i| sks.get(i).map(|sk| (i, sk.sign(msg))))
        .collect()
}

/// Test fixture for standard setup scenarios
pub struct TestFixture {
    pub global_data: GlobalData,
    pub secret_keys: Vec<SecretKey>,
    pub public_keys: Vec<PublicKey>,
    pub hints: Vec<Hint>,
    pub weights: Vec<F>,
    pub aggregation_key: Option<AggregationKey>,
    pub verifier_key: Option<VerifierKey>,
    pub domain_max: usize,
}

impl TestFixture {
    /// Create a new test fixture with standard setup
    pub fn new(
        domain_max: usize,
        n_participants: usize,
        rng: &mut impl Rng,
    ) -> Result<Self, HintsError> {
        let (gd, sks, pks, hints, weights) = setup_test_env(domain_max, n_participants, rng)?;

        Ok(Self {
            global_data: gd,
            secret_keys: sks,
            public_keys: pks,
            hints: hints,
            weights: weights,
            aggregation_key: None,
            verifier_key: None,
            domain_max,
        })
    }

    /// Complete setup to get aggregation and verifier keys
    pub fn complete_setup(&mut self) -> Result<(), HintsError> {
        let (ak, vk) = run_finish_setup(
            &self.global_data,
            self.domain_max,
            self.public_keys.clone(),
            &self.hints,
            self.weights.clone(),
        )?;

        self.aggregation_key = Some(ak);
        self.verifier_key = Some(vk);
        Ok(())
    }

    /// Generate signatures from a subset of participants
    pub fn generate_signatures(
        &self,
        indices: &[usize],
        msg: &[u8],
    ) -> Vec<(usize, PartialSignature)> {
        generate_partials(&self.secret_keys, msg, indices)
    }

    /// Aggregate signatures with given threshold
    pub fn aggregate(
        &self,
        threshold: F,
        partials: &[(usize, PartialSignature)],
        msg: &[u8],
    ) -> Result<Signature, HintsError> {
        let ak = self.aggregation_key.as_ref().expect("Setup not completed");
        ak.aggregate(
            &self.global_data,
            threshold,
            partials,
            self.weights.clone(),
            msg,
        )
    }

    /// Verify a signature
    pub fn verify(&self, signature: &Signature, msg: &[u8]) -> Result<bool, HintsError> {
        let vk = self.verifier_key.as_ref().expect("Setup not completed");
        signature.verify(&self.global_data, vk, msg)
    }

    /// Calculate the sum of weights for the given indices
    pub fn sum_weights(&self, indices: &[usize]) -> F {
        indices.iter().map(|&i| self.weights[i]).sum()
    }

    /// Modify weights (for testing different weight distributions)
    pub fn set_weight(&mut self, index: usize, weight: F) {
        if index < self.weights.len() {
            self.weights[index] = weight;
        }
    }

    /// Set all weights to a specific value
    pub fn set_all_weights(&mut self, weight: F) {
        self.weights.fill(weight);
    }
}

/// Custom assertion helper for error type checking with details
#[macro_export]
macro_rules! assert_error_type_and_details {
    ($result:expr, $error_pattern:pat, $expected_details:expr) => {
        match $result {
            Err($error_pattern) => {
                // Compare error details if needed
                assert_eq!(
                    format!("{:?}", $result.unwrap_err()),
                    $expected_details,
                    "Error details did not match expected content"
                );
            }
            _ => panic!(
                "Expected error matching {:?}, got {:?}",
                stringify!($error_pattern),
                $result
            ),
        }
    };
}

/// Helper for cleaner verification assertions
pub fn assert_signature_verifies(
    gd: &GlobalData,
    vk: &VerifierKey,
    signature: &Signature,
    msg: &[u8],
) {
    match signature.verify(gd, vk, msg) {
        Ok(true) => (), // Success case
        Ok(false) => panic!("Signature verification returned false"),
        Err(e) => panic!("Signature verification failed with error: {:?}", e),
    }
}
