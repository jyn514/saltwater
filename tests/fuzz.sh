#!/bin/sh
set -eu

if cargo +nightly >/dev/null 2>&1; then
	CARGO='cargo +nightly'
elif cargo --version | grep -q nightly; then
	CARGO='cargo'
else
	echo "cargo nightly is not installed, can't fuzz"
	exit 1
fi

exists() {
	which "$1" >/dev/null 2>&1
}

if ! exists cargo-fuzz; then
	$CARGO install cargo-fuzz
fi
$CARGO fuzz run libfuzzer -- -timeout=1 >/dev/null || true

if ! exists cargo-afl; then
	cargo install afl
fi
cd fuzz
RUSTFLAGS="-Clink-arg=-fuse-ld=gold" cargo afl build --bin afl
AFL_SKIP_CPUFREQ=1 timeout 120 cargo afl fuzz -i afl/inputs -o afl/outputs target/debug/afl || true
cat afl/outputs/crashes/* afl/outputs/hangs/* || true
cd ..
