#!/bin/sh
cargo run -- --color never input.c 2>&1 | grep "$1"
