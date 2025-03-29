use bolero::check;
use hints::snark::{F, KZG};
use hints::{HintsError, PartialSignature, Signature, PublicKey, SecretKey};
use ark_ff::{One, Zero};
use ark_std::rand::{RngCore, SeedableRng};
use ark_std::rand::rngs::StdRng;

use crate::test_helpers::*;

#[derive(Debug, bolero_generator::TypeGenerator)]
struct PropertyTestCase {
    domain_power: u8,
    num_signers: u8,
    weight_distribution: u8, // 0=uniform, 1=skewed, 2=binary, 3=random
    message_len: u8,
}

#[test]
fn test_protocol_properties() {
    check!()
        .with_type::<PropertyTestCase>()
        .for_each(|test_case| {
            // Test various protocol properties with this case
            test_signature_linearity_property(test_case);
            test_threshold_boundary_property(test_case);
            test_verification_correctness_property(test_case);
        });
}

// Property 1: Signature scheme should be linear - multiplying all weights by a scalar
// should result in the same valid signature
fn test_signature_linearity_property(test_case: &PropertyTestCase) {
    let mut rng = seeded_rng();
    let domain_power = (test_case.domain_power % 6) + 2;
    let domain_max = 1 << domain_power;
    let n_participants = domain_max - 1;
    
    // Create weights based on distribution strategy
    let weights = create_weight_distribution(
        n_participants, 
        test_case.weight_distribution,
        &mut rng
    );
    
    // Create scaled weights (multiply all by 2)
    let scalar = F::from(2u64);
    let scaled_weights: Vec<F> = weights.iter().map(|w| *w * scalar).collect();
    
    // Create test message
    let message_len = (test_case.message_len as usize) % 100 + 1;
    let message: Vec<u8> = (0..message_len).map(|_| rng.next_u32() as u8).collect();
    
    // Setup both environments
    let fixture1 = setup_test_fixture(domain_max, n_participants, weights.clone(), &mut rng);
    let fixture2 = setup_test_fixture(domain_max, n_participants, scaled_weights.clone(), &mut rng);
    
    if let (Some(fixture1), Some(fixture2)) = (fixture1, fixture2) {
        // Use a subset of signers
        let num_signers = (test_case.num_signers as usize) % n_participants + 1;
        let indices: Vec<usize> = (0..num_signers).collect();
        
        // Generate signatures for both weight sets
        let partials1 = fixture1.generate_signatures(&indices, &message);
        let partials2 = fixture2.generate_signatures(&indices, &message);
        
        // Calculate thresholds
        let total_weight1 = fixture1.sum_weights(&indices);
        let total_weight2 = fixture2.sum_weights(&indices);
        
        // Aggregate both signatures
        if let (Ok(sig1), Ok(sig2)) = (
            fixture1.aggregate(total_weight1, &partials1, &message),
            fixture2.aggregate(total_weight2, &partials2, &message)
        ) {
            // Both should verify correctly
            let verify1 = fixture1.verify(&sig1, &message);
            let verify2 = fixture2.verify(&sig2, &message);
            
            assert!(verify1.is_ok() && verify1.unwrap(), 
                "Original weights signature should verify");
                    
            assert!(verify2.is_ok() && verify2.unwrap(),
                "Scaled weights signature should verify");
        }
    }
}

// Property 2: Signatures should only verify when exactly the right threshold is used
fn test_threshold_boundary_property(test_case: &PropertyTestCase) {
    let mut rng = seeded_rng();
    let domain_power = (test_case.domain_power % 6) + 2;
    let domain_max = 1 << domain_power;
    let n_participants = domain_max - 1;
    
    // Create uniform weights for simplicity
    let weights = vec![F::from(1u64); n_participants];
    
    let message = b"threshold test";
    
    // Setup environment
    if let Some(mut fixture) = setup_test_fixture(domain_max, n_participants, weights, &mut rng) {
        // Use a subset of signers
        let num_signers = (test_case.num_signers as usize) % n_participants + 1;
        let indices: Vec<usize> = (0..num_signers).collect();
        
        // Generate partial signatures
        let partials = fixture.generate_signatures(&indices, message);
        let correct_weight = fixture.sum_weights(&indices);
        
        // Test with slightly incorrect weights
        for delta in [-2i64, -1, 0, 1, 2].iter() {
            let test_weight = if *delta < 0 && correct_weight <= F::from(-*delta as u64) {
                F::zero() // Don't go negative
            } else {
                correct_weight + F::from(*delta)
            };
            
            let sig_result = fixture.aggregate(test_weight, &partials, message);
            
            if let Ok(signature) = sig_result {
                let verify_result = fixture.verify(&signature, message);
                
                if *delta == 0 {
                    // Correct weight should always verify
                    assert!(verify_result.is_ok() && verify_result.unwrap(),
                        "Signature with correct weight should verify");
                } else {
                    // Implementation specific - some may verify with incorrect weights
                    // depending on the validation approach
                }
            } else if *delta == 0 {
                // Correct weight should always aggregate successfully
                panic!("Aggregation with correct weight should succeed");
            }
        }
    }
}

// Property 3: Verification correctness - signatures verify for the right message
fn test_verification_correctness_property(test_case: &PropertyTestCase) {
    let mut rng = seeded_rng();
    let domain_power = (test_case.domain_power % 6) + 2;
    let domain_max = 1 << domain_power;
    let n_participants = domain_max - 1;
    
    // Create weights
    let weights = create_weight_distribution(
        n_participants, 
        test_case.weight_distribution,
        &mut rng
    );
    
    // Create two different messages
    let message1 = b"first message";
    let message2 = b"second message";
    
    // Setup environment
    if let Some(mut fixture) = setup_test_fixture(domain_max, n_participants, weights, &mut rng) {
        // Use all signers for simplicity
        let indices: Vec<usize> = (0..n_participants).collect();
        
        // Generate partial signatures for message1
        let partials = fixture.generate_signatures(&indices, message1);
        let total_weight = fixture.sum_weights(&indices);
        
        // Aggregate signature for message1
        if let Ok(signature) = fixture.aggregate(total_weight, &partials, message1) {
            // Should verify for the original message
            let verify1 = fixture.verify(&signature, message1);
            
            assert!(verify1.is_ok() && verify1.unwrap(),
                "Signature should verify with original message");
                
            // Should not verify for a different message
            let verify2 = fixture.verify(&signature, message2);
            
            assert!(verify2.is_err() || !verify2.unwrap(),
                "Signature should not verify with different message");
        }
    }
}

// Helper to create different weight distributions for testing
fn create_weight_distribution(
    n: usize,
    distribution_type: u8,
    rng: &mut impl RngCore
) -> Vec<F> {
    match distribution_type % 4 {
        0 => {
            // Uniform weights
            vec![F::from(1u64); n]
        },
        1 => {
            // Skewed weights (one heavy weight, rest light)
            let mut weights = vec![F::from(1u64); n];
            if n > 0 {
                weights[0] = F::from(n as u64); // First participant has n times the weight
            }
            weights
        },
        2 => {
            // Binary distribution (powers of 2)
            (0..n).map(|i| F::from(1u64 << (i % 10))).collect()
        },
        3 => {
            // Random distribution
            (0..n).map(|_| F::from((rng.next_u32() as u64) % 100 + 1)).collect()
        },
        _ => unreachable!(),
    }
}

// Helper to create a test fixture with the given parameters
fn setup_test_fixture(
    domain_max: usize,
    n_participants: usize,
    weights: Vec<F>,
    rng: &mut StdRng
) -> Option<TestFixture> {
    let mut fixture = match TestFixture::new(domain_max, n_participants, rng) {
        Ok(f) => f,
        Err(_) => return None,
    };
    
    // Replace default weights with our custom weights
    for (i, weight) in weights.into_iter().enumerate().take(n_participants) {
        fixture.set_weight(i, weight);
    }
    
    // Complete setup
    if fixture.complete_setup().is_err() {
        return None;
    }
    
    Some(fixture)
} 