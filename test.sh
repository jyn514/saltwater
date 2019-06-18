set -e
set -v
cargo fmt -- --check
cargo clippy
cargo test
