#!/bin/bash
# Script to run the benchmarks and generate reports

cargo run --release --example save_committee 1024 benches/big_committee_bn254.json
cargo run --release --example transcode_committee benches/big_committee_bn254.json benches/big_committee_bn254.bincode

# Run with parallel feature (default)
echo "Running benchmarks with parallel feature enabled..."
cargo bench --features="parallel,asm"

# Run without parallel feature for comparison
echo "Running benchmarks without parallel feature for comparison..."
cargo bench --no-default-features --features="asm"

echo "Benchmark results are available in target/criterion/"
