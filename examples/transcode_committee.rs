use hints::*;

use ark_std::*;

use serde::{Deserialize, Serialize};
use std::env;
use std::io::Write;

#[derive(Serialize, Deserialize)]
struct Committee {
    pub pks: Vec<PublicKey>,
    pub weights: Vec<ark_serialize::CompressedChecked<snark::F>>,
    pub hints: Vec<Hint>,
    pub sks: Vec<SecretKey>,
    pub setup: UniverseSetup,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().collect();

    if args.len() != 3 {
        eprintln!("Usage: {} <input_file> <output_file>", args[0]);
        std::process::exit(1);
    }

    let input_file_path = &args[1];
    let output_file_path = &args[2];

    println!("Reading committee from: {}", input_file_path);
    let file = std::fs::File::open(input_file_path)
        .map_err(|e| format!("Failed to open input file: {}", e))?;

    let committee: Committee =
        serde_json::from_reader(file).map_err(|e| format!("Failed to parse committee: {}", e))?;

    println!("Writing committee to: {}", output_file_path);
    let output_file = std::fs::File::create(output_file_path)
        .map_err(|e| format!("Failed to create output file: {}", e))?;

    let mut buffered_writer = std::io::BufWriter::new(output_file);

    bincode::serde::encode_into_std_write(
        &committee,
        &mut buffered_writer,
        bincode::config::standard(),
    )
    .map_err(|e| format!("Failed to serialize committee: {}", e))?;

    buffered_writer.flush()?;
    println!("Transcoding completed successfully");

    Ok(())
}
