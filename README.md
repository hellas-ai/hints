# 🔐 hinTS: Threshold Signatures with Silent Setup 🤫

⚠️ This code has NOT been audited by anyone except the author. Use at your own risk! ⚠️ 

An implementation of [the hinTS paper](https://eprint.iacr.org/2023/567), heavily modified from the [research prototype](https://github.com/hintsrepo/hints).

## Overview

This library provides an efficient mechanism for aggregating BLS signatures ✍️ while verifying that a weighted threshold 🧮 is met. The "silent setup" 🤐 means that anyone can perform the aggregation — no communication needed between signers! 📡 All you need is the public keys of the participants 🪪 and a hint 🔍 that commits to their secret keys 🗝️. The threshold can be different for every message.

Built using ⚙️ arkworks for the cryptographic math 🧙‍♂️.

⚠️ This code has NOT been audited by anyone except the author. Use at your own risk! ⚠️

### Key Features

- **Silent Setup**: No DKG (Distributed Key Generation) protocol needed between signers
- **Dynamic Thresholds**: The threshold can be chosen after key generation, even for each message
- **Weighted Thresholds**: Native support for weighted signatures with no performance penalty
- **Efficient**: Signing takes ~1ms, verification ~17.5ms, aggregation under 0.5s for 1000 signers

## How It Works

hinTS is built on top of BLS signatures and uses Plonk-style arguments with KZG polynomial commitments to efficiently verify signature aggregation. At a high level:

1. Each signer generates a key pair locally and publishes a public key and a "hint"
2. BLS signatures are created normally for each message
3. An aggregator collects partial signatures, public keys, and hints
4. The aggregator creates a succinct proof that the combined weight of valid signatures exceeds the threshold
5. The final signature includes this proof and can be verified efficiently

## Example Usage

⚠️ This code has NOT been audited by anyone except the author. Use at your own risk! ⚠️

Here's a simple example of how to use hinTS:

```rust
use ark_std::{UniformRand, rand::Rng};
use hints::{*, snark::{finish_setup, F, Hint, KZG, GlobalData, SetupResult}};

fn sample_weights(n: usize, rng: &mut impl Rng) -> Vec<F> {
    (0..n).map(|_| F::from(u64::rand(rng))).collect()
}

// Generate random ("insecure") KZG setup
let mut rng = ark_std::test_rng();
let domain = 4; // Maximum number of signers
let n = 3;
let gd = GlobalData::from_params(domain, KZG::setup_insecure(domain, &mut rng).expect("Setup failed"));

// Generate keys for each participant
let sk: Vec<SecretKey> = (0..n).map(|_| SecretKey::random(&mut rng)).collect();
let pks: Vec<PublicKey> = sk.iter().map(|sk| sk.public(&gd)).collect();

// Generate hints for each participant
let hints: Vec<Hint> = sk.iter()
    .enumerate()
    .map(|(i, sk)| snark::hintgen(&gd, sk, domain, i).expect("Failed to generate hints"))
    .collect();

// Setup with weights
let weights = sample_weights(n, &mut rng);
let SetupResult { agg_key, vk, party_errors } = finish_setup(&gd, domain, pks, &hints, weights.clone())
    .expect("Failed to finish setup");

// Sign a message with each signer
let partials: Vec<(usize, PartialSignature)> = sk.iter()
    .enumerate()
    .map(|(i, sk)| (i, sk.sign(b"hello")))
    .collect();

// Aggregate signatures with a threshold of 1
let sig = agg_key.aggregate(&gd, F::from(1), &partials, weights, b"hello").unwrap();

// Verify the aggregated signature
let result = sig.verify(&gd, &vk, b"hello").unwrap();
assert!(result);
```

## Technical Details

hinTS uses several cryptographic primitives:

- **BLS Signatures**: For basic signature operations
- **KZG Polynomial Commitments**: For efficient proofs about polynomials
- **Plonk-style Arguments**: For verifying signature aggregation
- **Arkworks Libraries**: For underlying elliptic curve operations

The security of hinTS is proven in the Algebraic Group Model and relies on the q-Decisional Diffie-Hellman Inversion assumption.

## Performance

Performance metrics on a standard machine:
- Signing: ~1ms per signature (constant time)
- Verification: ~17.5ms (constant time)
- Aggregation: <0.5s for 1000 signers
