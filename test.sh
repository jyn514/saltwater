set -e
set -v
cargo fmt -- --check
cargo test
cargo clean
cargo clippy
