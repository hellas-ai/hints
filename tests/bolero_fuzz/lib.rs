// Main fuzz test module
pub mod hints_fuzz;

// Component-specific fuzz tests
pub mod components {
    pub mod property_tests;
}

// Model-based mutation tests
pub mod models {
    pub mod signature_mutator;
}

// Exhaustive permutation tests
pub mod exhaustive {
    pub mod subset_tests;
    pub mod combinatorial;
}

// Main fuzz tests
pub mod subset_tests; 

// Import test helpers
#[path = "../test_helpers.rs"]
mod test_helpers;