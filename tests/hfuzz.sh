#!/bin/sh
cd "$(git rev-parse --show-toplevel)"/examples
cargo hfuzz build
cargo hfuzz run hfuzz
