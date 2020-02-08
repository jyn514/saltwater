#!/bin/sh
cargo install honggfuzz
cargo hfuzz build
cargo hfuzz run hfuzz
