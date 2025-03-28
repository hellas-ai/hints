use core::hint::black_box;

use hints::snark::*;
use hints::*;

use ark_std::rand::Rng;
use ark_std::*;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

fn sample_secret_keys(num_parties: usize) -> Vec<SecretKey> {
    let mut rng = test_rng();
    let mut keys = vec![];
    for _ in 0..num_parties {
        keys.push(SecretKey::random(&mut rng));
    }
    keys
}

fn sample_weights(n: usize) -> Vec<F> {
    let mut rng = &mut test_rng();
    (0..n).map(|_| F::from(u64::rand(&mut rng))).collect()
}

/// n is the size of the bitmap, and probability is for true or 1.
fn sample_bitmap(n: usize, probability: f64) -> Vec<F> {
    let mut rng = &mut test_rng();
    let mut bitmap = vec![];
    for _i in 0..n {
        let r = f64::rand(&mut rng);
        if r < probability {
            bitmap.push(F::one());
        } else {
            bitmap.push(F::zero());
        }
    }
    bitmap
}

pub fn main() {
    let n = 128;
    println!("n = {}", n);

    // -------------- sample one-time SRS ---------------
    //run KZG setup
    let rng = &mut ark_std::test_rng();

    let setup = start_timer!(|| "KZG Setup");
    let gd = GlobalData::from_params(n, KZG::setup_insecure(n, rng).expect("Setup failed"));
    end_timer!(setup);

    // -------------- sample universe specific values ---------------
    //sample random keys
    let sk: Vec<SecretKey> = sample_secret_keys(n - 1);

    let pks: Vec<PublicKey> = sk.iter().map(|sk| sk.public(&gd)).collect();

    //sample random weights for each party
    let weights = sample_weights(n - 1);

    // -------------- perform universe setup ---------------
    //run universe setup

    let parallel_work = start_timer!(|| "Hint generation");

    #[cfg(not(feature = "parallel"))]
    let hints: Vec<Hint> = sk
        .iter()
        .enumerate()
        .map(|(i, sk)| hintgen(&gd, sk, n, i).expect("Failed to generate hints"))
        .collect();

    #[cfg(feature = "parallel")]
    let hints: Vec<Hint> = sk
        .par_iter()
        .enumerate()
        .map(|(i, sk)| hintgen(&gd, sk, n, i).expect("Failed to generate hints"))
        .collect();

    end_timer!(parallel_work);

    let setup = start_timer!(|| "Setup");
    let (ak, vk, hint_errors) =
        finish_setup(&gd, n, pks, &hints, weights.clone()).expect("Failed to finish setup");
    end_timer!(setup);

    assert_eq!(
        hint_errors.len(),
        0,
        "Hint generation was not consistent with the finished setup: {:?}",
        hint_errors
    );

    // -------------- sample proof specific values ---------------
    //samples n-1 random bits
    let bitmap = sample_bitmap(n - 1, 0.9);

    let proving = start_timer!(|| "SNARK proof generation");
    let proof = black_box(prove(&gd.params, &gd.cache, &ak, weights.clone(), bitmap).unwrap());
    end_timer!(proving);

    let verification = start_timer!(|| "SNARK proof verification");
    assert!(
        verify_proof(&vk, &proof).expect("Failed to verify proof"),
        "Proof is invalid"
    );
    end_timer!(verification);

    let signing = start_timer!(|| "Signature generation");
    let partials: Vec<(usize, PartialSignature)> = sk
        .iter()
        .enumerate()
        .map(|(i, sk)| (i, sign(sk, b"hello")))
        .collect();
    end_timer!(signing);

    let aggregation = start_timer!(|| "Signature aggregation");
    let sig = sign_aggregate(&gd, &ak, F::one(), &partials, weights, b"hello").unwrap();
    end_timer!(aggregation);

    let verification = start_timer!(|| "Signature verification");
    assert!(
        verify_aggregate(&vk, &sig, b"hello").unwrap(),
        "Signature is invalid"
    );
    end_timer!(verification);

    println!("All good!");
}
