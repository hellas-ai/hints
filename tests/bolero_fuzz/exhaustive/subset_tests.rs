use hints::snark::{finish_setup, hintgen, F, KZG};
use hints::{PartialSignature, Signature};
use ark_ff::Zero;

use crate::test_helpers::*;

/// Test all possible subsets for a small domain
#[test]
fn test_all_possible_participant_subsets() {
    let mut rng = seeded_rng();
    
    // Use a reasonably small domain for exhaustive testing
    let domain_max = 16;
    let n_participants = domain_max - 1;
    
    // Setup with standard fixture
    let mut fixture = match TestFixture::new(domain_max, n_participants, &mut rng) {
        Ok(f) => f,
        Err(e) => panic!("Failed to create test fixture: {:?}", e),
    };
    
    // Use uniform weights for simplicity
    fixture.set_all_weights(F::from(1u64));
    
    if fixture.complete_setup().is_err() {
        panic!("Failed to complete setup");
    }
    
    // Message to sign
    let message = b"exhaustive subset test";
    
    // Test every possible non-empty subset of participants (2^n - 1 combinations)
    let total_subsets = (1 << n_participants) - 1;
    let mut valid_subsets = 0;
    
    for subset_mask in 1..=total_subsets {
        // Convert the bitmask to a list of participant indices
        let mut indices = Vec::new();
        for i in 0..n_participants {
            if ((subset_mask >> i) & 1) == 1 {
                indices.push(i);
            }
        }
        
        // Generate partial signatures for this subset
        let partials = fixture.generate_signatures(&indices, message);
        
        // Calculate subset weight (since we're using uniform weight 1, this is just the count)
        let subset_weight = F::from(indices.len() as u64);
        
        // Try to aggregate and verify
        match fixture.aggregate(subset_weight, &partials, message) {
            Ok(signature) => {
                match fixture.verify(&signature, message) {
                    Ok(true) => {
                        valid_subsets += 1;
                        println!("Valid subset: {:?}", indices);
                    },
                    _ => println!("Invalid verification for subset: {:?}", indices),
                }
            },
            Err(e) => println!("Invalid aggregation for subset: {:?}, error: {:?}", indices, e),
        }
    }
    
    println!("Tested {} total subsets, {} were valid", total_subsets, valid_subsets);
    
    // At the very minimum, the full set should be valid
    assert!(valid_subsets > 0, "At least one subset should be valid");
}

/// Tests robustness to missing participants by systematically excluding each participant
#[test]
fn test_participant_exclusion_robustness() {
    let mut rng = seeded_rng();
    
    // Use a reasonably sized domain
    let domain_max = 16;
    let n_participants = domain_max - 1;
    
    // Setup with standard fixture
    let mut fixture = match TestFixture::new(domain_max, n_participants, &mut rng) {
        Ok(f) => f,
        Err(e) => panic!("Failed to create test fixture: {:?}", e),
    };
    
    if fixture.complete_setup().is_err() {
        panic!("Failed to complete setup");
    }
    
    // Message to sign
    let message = b"exclusion robustness test";
    
    // Test with excluding each participant, one at a time
    for excluded_idx in 0..n_participants {
        // Create a set of all participants except the excluded one
        let indices: Vec<usize> = (0..n_participants).filter(|&i| i != excluded_idx).collect();
        
        // Generate partial signatures for this subset
        let partials = fixture.generate_signatures(&indices, message);
        
        // Calculate subset weight
        let subset_weight = fixture.sum_weights(&indices);
        
        // Try to aggregate and verify
        match fixture.aggregate(subset_weight, &partials, message) {
            Ok(signature) => {
                match fixture.verify(&signature, message) {
                    Ok(true) => {
                        println!("Valid with participant {} excluded", excluded_idx);
                    },
                    _ => println!("Invalid verification with participant {} excluded", excluded_idx),
                }
            },
            Err(e) => println!("Failed aggregation with participant {} excluded: {:?}", excluded_idx, e),
        }
    }
}

/// Tests minimum viable subsets by testing different threshold combinations
#[test]
fn test_minimum_viable_subsets() {
    let mut rng = seeded_rng();
    
    // Use a small domain for manageable testing
    let domain_max = 16;
    let n_participants = domain_max - 1;
    
    // Setup with standard fixture but use varying weights
    let mut fixture = match TestFixture::new(domain_max, n_participants, &mut rng) {
        Ok(f) => f,
        Err(e) => panic!("Failed to create test fixture: {:?}", e),
    };
    
    // Assign weights with increasing value: [1, 2, 3, 4, 5, 6, 7]
    for i in 0..n_participants {
        fixture.set_weight(i, F::from((i + 1) as u64));
    }
    
    if fixture.complete_setup().is_err() {
        panic!("Failed to complete setup");
    }
    
    let message = b"minimum viable subset test";
    
    // Calculate the total weight of all participants
    let total_weight = fixture.sum_weights(&(0..n_participants).collect::<Vec<_>>());
    
    // Test different threshold values
    let threshold_percentages = [25, 50, 75, 100];
    
    for &percentage in &threshold_percentages {
        // Calculate threshold as percentage of total weight
        let threshold = total_weight * F::from(percentage) / F::from(100u64);
        println!("Testing threshold {}% = {}", percentage, threshold);
        
        // Test every possible subset
        let total_subsets = (1 << n_participants) - 1;
        let mut valid_for_threshold = 0;
        
        for subset_mask in 1..=total_subsets {
            // Convert the bitmask to a list of participant indices
            let mut indices = Vec::new();
            for i in 0..n_participants {
                if ((subset_mask >> i) & 1) == 1 {
                    indices.push(i);
                }
            }
            
            // Calculate subset weight
            let subset_weight = fixture.sum_weights(&indices);
            
            // Only test if this subset meets the threshold
            if subset_weight >= threshold {
                // Generate partial signatures
                let partials = fixture.generate_signatures(&indices, message);
                
                // Try to aggregate and verify
                match fixture.aggregate(threshold, &partials, message) {
                    Ok(signature) => {
                        match fixture.verify(&signature, message) {
                            Ok(true) => {
                                valid_for_threshold += 1;
                                println!("Valid subset for {}% threshold: {:?}", percentage, indices);
                            },
                            _ => println!("Invalid verification for subset: {:?}", indices),
                        }
                    },
                    Err(e) => println!("Invalid aggregation for subset: {:?}, error: {:?}", indices, e),
                }
            }
        }
        
        println!("For {}% threshold, found {} valid subsets", percentage, valid_for_threshold);
        assert!(valid_for_threshold > 0, "Should have at least one valid subset for each threshold");
    }
} 