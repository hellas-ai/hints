use ark_serialize::CompressedChecked;
use hints::snark::*;
use hints::*;

use ark_std::*;

use serde::{Deserialize, Serialize};
use std::io::Write;
use std::{env, time::Instant};

use rayon::prelude::*;

#[derive(Serialize, Deserialize)]
struct Committee {
    pub pks: Vec<PublicKey>,
    pub weights: Vec<CompressedChecked<F>>,
    pub hints: Vec<Hint>,
    pub sks: Vec<SecretKey>,
    pub setup: UniverseSetup,
}

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

pub fn main() {
    let start = Instant::now();
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 && args.len() != 3 {
        eprintln!("Usage: {} <n> [output_file]", args[0]);
        std::process::exit(1);
    }

    let output_file: Box<dyn Write> = if args.len() == 3 {
        Box::new(std::fs::File::create(&args[2]).expect("Failed to create output file"))
    } else {
        Box::new(std::io::stdout().lock())
    };

    let n = args[1]
        .parse::<usize>()
        .expect("Failed to parse n as usize");

    let rng = &mut ark_std::test_rng();

    let gd = GlobalData::new(n, rng).expect("Setup failed");

    let sk: Vec<SecretKey> = sample_secret_keys(n - 1);

    let pks: Vec<PublicKey> = sk.iter().map(|sk| sk.public(&gd)).collect();

    let weights = sample_weights(n - 1);

    let hints: Vec<Hint> = sk
        .par_iter()
        .enumerate()
        .map(|(i, sk)| generate_hint(&gd, sk, n, i).expect("Failed to generate hints"))
        .collect();

    let univ_setup =
        setup_universe(&gd, pks.clone(), &hints, weights.clone()).expect("Failed to finish setup");

    assert_eq!(
        univ_setup.party_errors.len(),
        0,
        "Hint generation was not consistent with the finished setup: {:?}",
        univ_setup.party_errors
    );

    // Create and serialize the Committee struct
    let committee = Committee {
        pks,
        weights: weights
            .iter()
            .map(|w| CompressedChecked::from(*w))
            .collect(),
        hints,
        sks: sk,
        setup: univ_setup,
    };

    let json = serde_json::to_string_pretty(&committee).expect("Failed to serialize committee");
    writeln!(std::io::BufWriter::new(output_file), "{}", json).expect("Failed to write to file");
    println!("Time taken: {:.3}s", start.elapsed().as_secs_f64());
}
