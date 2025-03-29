//! Optimized test framework for the Hints protocol with centralized caching.
//!
//! This framework eliminates boilerplate and minimizes expensive operations by:
//! 1. Caching GlobalData instances for different domain sizes
//! 2. Centralizing secret key and hint generation
//! 3. Providing test builders with fluent interfaces
//! 4. Standardizing common test patterns

use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Mutex;
use std::sync::Once;
use std::time::Instant;

use crate::snark::{
    finish_setup, hintgen, AggregationKey, GlobalData, Hint, SetupResult, VerifierKey, F, G1, G2,
    KZG,
};
use crate::{HintsError, PartialSignature, PublicKey, SecretKey, Signature};

use ark_ff::PrimeField;
use ark_ff::{Field, One, UniformRand, Zero};
use ark_std::{
    ops::*,
    rand::{rngs::StdRng, Rng, SeedableRng},
    vec,
    vec::Vec,
};
use once_cell::sync::Lazy;

// === Global Cache ===

/// Test seed for deterministic RNG
const TEST_SEED: [u8; 32] = [42u8; 32];

/// The maximum domain power we expect to use (2^10 = 1024)
const MAX_DOMAIN_POWER: u32 = 10;

/// Creates a deterministic RNG for tests
pub fn seeded_rng() -> StdRng {
    StdRng::from_seed(TEST_SEED)
}

/// Global cache for KZG and GlobalData instances, keyed by domain_max
static GLOBAL_DATA_CACHE: Lazy<Mutex<HashMap<usize, GlobalData>>> = Lazy::new(|| {
    let mut cache = HashMap::new();
    let mut rng = seeded_rng();

    // Pre-populate cache with common domain sizes (powers of 2)
    for power in 1..=MAX_DOMAIN_POWER {
        let domain_max = 1 << power;
        if let Ok(kzg) = KZG::setup_insecure(domain_max, &mut rng) {
            cache.insert(domain_max, GlobalData::from_params(domain_max, kzg));
        }
    }

    Mutex::new(cache)
});

/// Global cache for key pairs and hints
static KEY_CACHE: Lazy<Mutex<HashMap<(usize, usize), (SecretKey, PublicKey, Hint)>>> =
    Lazy::new(|| Mutex::new(HashMap::new()));

/// Gets a cached GlobalData instance or creates a new one
pub fn get_global_data(domain_max: usize) -> Result<GlobalData, HintsError> {
    if !domain_max.is_power_of_two() || domain_max == 0 {
        return Err(HintsError::InvalidInput(
            "domain_max must be a power of 2 and > 0".to_string(),
        ));
    }

    let mut cache = GLOBAL_DATA_CACHE.lock().unwrap();

    if let Some(gd) = cache.get(&domain_max) {
        Ok(gd.clone())
    } else {
        let mut rng = seeded_rng();
        let kzg = KZG::setup_insecure(domain_max, &mut rng)?;
        let gd = GlobalData::from_params(domain_max, kzg);
        cache.insert(domain_max, gd.clone());
        Ok(gd)
    }
}

/// Gets or generates a key pair and hint for a participant
fn get_or_create_participant(
    global_data: &GlobalData,
    domain_max: usize,
    participant_idx: usize,
) -> Result<(SecretKey, PublicKey, Hint), HintsError> {
    let mut cache = KEY_CACHE.lock().unwrap();
    let key = (domain_max, participant_idx);

    if let Some(data) = cache.get(&key) {
        Ok(data.clone())
    } else {
        let mut rng = seeded_rng();
        let secret_key = SecretKey::random(&mut rng);
        let public_key = secret_key.public(global_data);
        let hint = hintgen(global_data, &secret_key, domain_max, participant_idx)?;

        let data = (secret_key, public_key, hint);
        cache.insert(key, data.clone());
        Ok(data)
    }
}

// === Weight Generation Strategies ===

/// Strategies for generating participant weights
#[derive(Clone, Debug)]
pub enum WeightStrategy {
    /// All participants have the same weight
    Uniform(u64),
    /// One participant has a much higher weight
    Skewed {
        dominant_idx: usize,
        dominant_weight: u64,
        others: u64,
    },
    /// Weights are powers of 2
    Binary,
    /// Random weights within a range
    Random { min: u64, max: u64 },
    /// Zero weights for specific participants
    WithZeros {
        default: u64,
        zero_indices: &'static [usize],
    },
    /// Custom weights specified directly
    Custom(Vec<u64>),
}

impl WeightStrategy {
    /// Generate weights according to the strategy
    pub fn generate(&self, n_participants: usize, rng: &mut impl Rng) -> Vec<F> {
        match self {
            WeightStrategy::Uniform(weight) => {
                vec![F::from(*weight); n_participants]
            }
            WeightStrategy::Skewed {
                dominant_idx,
                dominant_weight,
                others,
            } => {
                let mut weights = vec![F::from(*others); n_participants];
                if *dominant_idx < n_participants {
                    weights[*dominant_idx] = F::from(*dominant_weight);
                }
                weights
            }
            WeightStrategy::Binary => (0..n_participants)
                .map(|i| F::from(1u64 << (i % 16)))
                .collect(),
            WeightStrategy::Random { min, max } => (0..n_participants)
                .map(|_| {
                    let weight = rng.gen_range(*min..=*max);
                    F::from(weight)
                })
                .collect(),
            WeightStrategy::WithZeros {
                default,
                zero_indices,
            } => {
                let mut weights = vec![F::from(*default); n_participants];
                for &idx in *zero_indices {
                    if idx < n_participants {
                        weights[idx] = F::zero();
                    }
                }
                weights
            }
            WeightStrategy::Custom(weights) => {
                let mut result = Vec::with_capacity(n_participants);
                for i in 0..n_participants {
                    let weight = if i < weights.len() {
                        weights[i]
                    } else {
                        1 // Default to 1 if custom weights are exhausted
                    };
                    result.push(F::from(weight));
                }
                result
            }
        }
    }
}

// === Test Environment ===

/// Wrapper around setup result for easier testing
pub struct TestEnvironment {
    /// GlobalData instance
    pub global_data: GlobalData,
    /// Domain size (must be power of 2)
    pub domain_max: usize,
    /// Number of participants (domain_max - 1)
    pub n_participants: usize,
    /// Secret keys for all participants
    pub secret_keys: Vec<SecretKey>,
    /// Public keys for all participants
    pub public_keys: Vec<PublicKey>,
    /// Hints for all participants
    pub hints: Vec<Hint>,
    /// Weights for all participants
    pub weights: Vec<F>,
    /// Aggregation key (after setup)
    pub aggregation_key: Option<AggregationKey>,
    /// Verifier key (after setup)
    pub verifier_key: Option<VerifierKey>,
    /// Party errors from setup
    pub party_errors: Vec<(usize, crate::PartyError)>,
}

impl TestEnvironment {
    /// Create a new test environment with caching optimizations
    pub fn new(domain_power: u32, weight_strategy: WeightStrategy) -> Result<Self, HintsError> {
        let domain_max = 1 << domain_power;
        let n_participants = domain_max - 1;

        // Get GlobalData from cache
        let global_data = get_global_data(domain_max)?;

        // Get or create all participants
        let mut secret_keys = Vec::with_capacity(n_participants);
        let mut public_keys = Vec::with_capacity(n_participants);
        let mut hints = Vec::with_capacity(n_participants);

        for i in 0..n_participants {
            let (sk, pk, hint) = get_or_create_participant(&global_data, domain_max, i)?;
            secret_keys.push(sk);
            public_keys.push(pk);
            hints.push(hint);
        }

        // Generate weights
        let mut rng = seeded_rng();
        let weights = weight_strategy.generate(n_participants, &mut rng);

        Ok(Self {
            global_data,
            domain_max,
            n_participants,
            secret_keys,
            public_keys,
            hints,
            weights,
            aggregation_key: None,
            verifier_key: None,
            party_errors: Vec::new(),
        })
    }

    /// Complete setup to get aggregation and verifier keys
    pub fn complete_setup(&mut self) -> Result<(), HintsError> {
        let result = finish_setup(
            &self.global_data,
            self.domain_max,
            self.public_keys.clone(),
            &self.hints,
            self.weights.clone(),
        )?;

        self.aggregation_key = Some(result.agg_key);
        self.verifier_key = Some(result.vk);
        self.party_errors = result.party_errors;

        Ok(())
    }

    /// Get a specific weight or zero if out of bounds
    pub fn weight(&self, idx: usize) -> F {
        if idx < self.weights.len() {
            self.weights[idx]
        } else {
            F::zero()
        }
    }

    /// Calculate sum of weights for given indices
    pub fn sum_weights(&self, indices: &[usize]) -> F {
        indices
            .iter()
            .filter(|&&i| i < self.weights.len())
            .map(|&i| self.weights[i])
            .fold(F::zero(), |acc, w| acc + w)
    }

    /// Generate partial signatures for given indices
    pub fn generate_partial_signatures(
        &self,
        indices: &[usize],
        message: &[u8],
    ) -> Vec<(usize, PartialSignature)> {
        indices
            .iter()
            .filter_map(|&i| {
                if i < self.secret_keys.len() {
                    Some((i, self.secret_keys[i].sign(message)))
                } else {
                    None
                }
            })
            .collect()
    }

    /// Aggregate partial signatures
    pub fn aggregate(
        &self,
        threshold: F,
        partials: &[(usize, PartialSignature)],
        message: &[u8],
    ) -> Result<Signature, HintsError> {
        let agg_key = self
            .aggregation_key
            .as_ref()
            .ok_or_else(|| HintsError::InvalidInput("Setup not completed".to_string()))?;

        agg_key.aggregate(
            &self.global_data,
            threshold,
            partials,
            self.weights.clone(),
            message,
        )
    }

    /// Verify a signature
    pub fn verify(&self, signature: &Signature, message: &[u8]) -> Result<bool, HintsError> {
        let vk = self
            .verifier_key
            .as_ref()
            .ok_or_else(|| HintsError::InvalidInput("Setup not completed".to_string()))?;

        signature.verify(&self.global_data, vk, message)
    }
}

// === Test Builder ===

/// Builder for test cases to reduce boilerplate
pub struct TestCaseBuilder {
    domain_power: u32,
    weight_strategy: WeightStrategy,
    signer_indices: Vec<usize>,
    message: Cow<'static, [u8]>,
    threshold_strategy: ThresholdStrategy,
    expected_outcome: ExpectedOutcome,
}

/// Strategies for threshold calculation
#[derive(Clone, Copy, Debug)]
pub enum ThresholdStrategy {
    /// Exact sum of weights for the signers
    Exact,
    /// Slightly above the sum (by delta)
    Above(u64),
    /// Slightly below the sum (by delta)
    Below(u64),
    /// Fixed value
    Fixed(u64),
    /// Percentage of total weight
    Percentage(u8),
}

/// Expected test outcomes
#[derive(Clone, Copy, Debug)]
pub enum ExpectedOutcome {
    /// Expect successful aggregation and verification
    Success,
    /// Expect threshold not met error
    ThresholdNotMet,
    /// Expect verification to fail
    VerificationFailed,
    /// Expect any failure
    AnyFailure,
}

impl TestCaseBuilder {
    /// Create a new test case builder with default values
    pub fn new() -> Self {
        Self {
            domain_power: 3, // 2^3 = 8 by default
            weight_strategy: WeightStrategy::Uniform(1),
            signer_indices: vec![0, 1, 2],
            message: Cow::Borrowed(b"test message"),
            threshold_strategy: ThresholdStrategy::Exact,
            expected_outcome: ExpectedOutcome::Success,
        }
    }

    /// Set domain power (domain_max = 2^power)
    pub fn domain_power(mut self, power: u32) -> Self {
        self.domain_power = power;
        self
    }

    /// Set weight generation strategy
    pub fn weights(mut self, strategy: WeightStrategy) -> Self {
        self.weight_strategy = strategy;
        self
    }

    /// Set which participants will sign
    pub fn signers(mut self, indices: Vec<usize>) -> Self {
        self.signer_indices = indices;
        self
    }

    /// Set the message to sign
    pub fn message(mut self, msg: impl Into<Vec<u8>>) -> Self {
        self.message = Cow::Owned(msg.into());
        self
    }

    /// Set threshold calculation strategy
    pub fn threshold(mut self, strategy: ThresholdStrategy) -> Self {
        self.threshold_strategy = strategy;
        self
    }

    /// Set expected outcome
    pub fn expect(mut self, outcome: ExpectedOutcome) -> Self {
        self.expected_outcome = outcome;
        self
    }

    /// Execute the test case
    pub fn run(self) -> Result<(), String> {
        // Set up the test environment
        let mut env = TestEnvironment::new(self.domain_power, self.weight_strategy)
            .map_err(|e| format!("Failed to create test environment: {:?}", e))?;

        env.complete_setup()
            .map_err(|e| format!("Setup failed: {:?}", e))?;

        // Generate partial signatures
        let partials = env.generate_partial_signatures(&self.signer_indices, &self.message);

        // Calculate threshold
        let signer_weight = env.sum_weights(&self.signer_indices);
        let threshold = match self.threshold_strategy {
            ThresholdStrategy::Exact => signer_weight,
            ThresholdStrategy::Above(delta) => signer_weight + F::from(delta),
            ThresholdStrategy::Below(delta) => {
                if let Some(diff) = signer_weight.try_sub(&F::from(delta)) {
                    diff
                } else {
                    F::zero() // If delta is larger than sum, use zero
                }
            }
            ThresholdStrategy::Fixed(value) => F::from(value),
            ThresholdStrategy::Percentage(percent) => {
                let total_weight = env.sum_weights(&(0..env.n_participants).collect::<Vec<_>>());
                let tw: u64 = total_weight.into_bigint().0[0];
                let scaled = (tw as f64) * (percent as f64 / 100.0);

                F::from(scaled as u64)
            }
        };

        // Run aggregation
        let agg_result = env.aggregate(threshold, &partials, &self.message);

        // Check result against expected outcome
        match (agg_result, self.expected_outcome) {
            (Ok(signature), ExpectedOutcome::Success) => {
                // Expect verification to succeed
                match env.verify(&signature, &self.message) {
                    Ok(true) => Ok(()),
                    Ok(false) => Err("Signature verification returned false".to_string()),
                    Err(e) => Err(format!("Verification failed: {:?}", e)),
                }
            }
            (Ok(_), ExpectedOutcome::ThresholdNotMet) => {
                Err("Expected ThresholdNotMet but aggregation succeeded".to_string())
            }
            (Ok(signature), ExpectedOutcome::VerificationFailed) => {
                // Expect verification to fail
                match env.verify(&signature, &self.message) {
                    Ok(false) | Err(_) => Ok(()),
                    Ok(true) => Err("Expected verification to fail but it succeeded".to_string()),
                }
            }
            (Err(HintsError::ThresholdNotMet), ExpectedOutcome::ThresholdNotMet) => {
                Ok(()) // Expected threshold not met error
            }
            (Err(_), ExpectedOutcome::AnyFailure) => {
                Ok(()) // Any error is fine
            }
            (Err(e), _) => Err(format!("Unexpected error: {:?}", e)),
            (Ok(_), ExpectedOutcome::AnyFailure) => {
                Err("Expected failure but got success".to_string())
            }
        }
    }
}

// === Test Components ===

/// Performance tracker for measuring operation times
pub struct PerformanceTracker {
    timings: RefCell<HashMap<&'static str, Vec<std::time::Duration>>>,
}

impl PerformanceTracker {
    /// Create a new performance tracker
    pub fn new() -> Self {
        Self {
            timings: RefCell::new(HashMap::new()),
        }
    }

    /// Track the execution time of an operation
    pub fn measure<T, F: FnOnce() -> T>(&self, name: &'static str, f: F) -> T {
        let start = Instant::now();
        let result = f();
        let duration = start.elapsed();

        self.timings
            .borrow_mut()
            .entry(name)
            .or_insert_with(Vec::new)
            .push(duration);

        result
    }

    /// Get average execution time for an operation
    pub fn average(&self, name: &'static str) -> Option<std::time::Duration> {
        let timings = self.timings.borrow();
        let times = timings.get(name)?;

        if times.is_empty() {
            return None;
        }

        let total_nanos: u128 = times.iter().map(|d| d.as_nanos()).sum();
        let avg_nanos = total_nanos / times.len() as u128;

        Some(std::time::Duration::from_nanos(avg_nanos as u64))
    }

    /// Print performance statistics
    pub fn print_stats(&self) {
        let timings = self.timings.borrow();
        println!("Performance Statistics:");

        for (name, times) in timings.iter() {
            if times.is_empty() {
                continue;
            }

            let total_nanos: u128 = times.iter().map(|d| d.as_nanos()).sum();
            let avg_nanos = total_nanos / times.len() as u128;
            let min_nanos = times.iter().map(|d| d.as_nanos()).min().unwrap_or(0);
            let max_nanos = times.iter().map(|d| d.as_nanos()).max().unwrap_or(0);

            println!(
                "{}: calls={}, avg={:?}, min={:?}, max={:?}",
                name,
                times.len(),
                std::time::Duration::from_nanos(avg_nanos as u64),
                std::time::Duration::from_nanos(min_nanos as u64),
                std::time::Duration::from_nanos(max_nanos as u64),
            );
        }
    }
}

// === Utility Extension Traits ===

/// Extension trait for F to add ease-of-use methods
pub trait FieldExt {
    /// Try to subtract without underflow
    fn try_sub(&self, other: &Self) -> Option<Self>
    where
        Self: Sized;
}

impl FieldExt for F {
    fn try_sub(&self, other: &Self) -> Option<Self> {
        if self >= other {
            Some(*self - *other)
        } else {
            None
        }
    }
}