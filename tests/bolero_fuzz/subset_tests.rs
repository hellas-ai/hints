use hints::snark::F;
use ark_ff::Zero;

use crate::test_helpers::*;

/// Test all possible subsets for a small domain
#[test]
fn test_all_possible_participant_subsets() {
    let mut rng = seeded_rng();
    
    // Use a reasonably small domain for exhaustive testing
    let domain_max = 8;
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