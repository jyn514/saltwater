#!/bin/sh
cargo run --quiet -- --color never --max-errors 0 input.c 2>&1
