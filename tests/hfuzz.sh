#!/bin/sh
cd "$(git rev-parse --show-toplevel)"/examples
cargo install hfuzz
cargo hfuzz build
cargo hfuzz run hfuzz
