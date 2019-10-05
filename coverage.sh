#!/bin/sh
set -eu
rm -f target/debug/*-*
RUSTFLAGS='-C debuginfo=2' cargo test --no-run
ls -1 target/debug/*-* \
	| grep -v '\.d$' \
	| xargs -n1 kcov --verify target/cov
xdg-open target/cov/index.html
