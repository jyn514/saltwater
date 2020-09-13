#!/bin/sh
set -ev
cargo fmt --all -- --check
cargo clippy --all --all-features -- -D clippy::all -D unused-imports
cargo test --all --all-features
