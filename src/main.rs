use std::time::Instant;

use ark_std::test_rng;

fn main() {
    println!("Running original proof system, ported...");
    hints::original_proof_system::main();
    println!("Running SonigKZG proof system...");
    hints::proof_system::main();
    println!("Running original code system...");
    hints::original_code::main();
}