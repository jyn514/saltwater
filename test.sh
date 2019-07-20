set -ev
cargo fmt -- --check
cargo clippy -- -D clippy::all
cargo test
