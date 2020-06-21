#!/bin/sh
cargo run --release --quiet -- --color never --max-errors 0 input.c 2>&1
