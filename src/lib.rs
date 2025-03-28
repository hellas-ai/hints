
pub mod kzg;
pub mod utils;
pub mod proof_system;

// Public interface for using this crate in a more user-friendly way
pub struct UniverseBuilder;
pub struct Universe;
pub struct PartialSignature;
pub struct WeightedThresholdSignature;

impl Universe {
    pub fn sign(&self, message: &[u8]) -> PartialSignature {
        todo!()
    }

    pub fn verify_partial(&self, message: &[u8], partial_signature: &PartialSignature) -> bool {
        todo!()
    }

    pub fn sign_aggregate(&self, message: &[u8], partials: &[PartialSignature]) -> WeightedThresholdSignature {
        todo!()
    }
}

#[cfg(test)]
mod test;