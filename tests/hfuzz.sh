#!/bin/sh
ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT/fuzz"

cargo install honggfuzz
cargo hfuzz run hfuzz
