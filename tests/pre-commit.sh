#!/bin/sh
cd parser
set -ev
cargo fmt -- --check
cargo clippy -- -D clippy::all -D unused-imports
cargo test
