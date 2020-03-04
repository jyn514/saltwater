#!/bin/sh
ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT/fuzz"

# honggfuzz can't handle absolute paths
case "$CARGO_TARGET_DIR" in
	/*) unset CARGO_TARGET_DIR ;;
esac

cargo install honggfuzz
cargo hfuzz run hfuzz
