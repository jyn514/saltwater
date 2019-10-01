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
if ! [ "$(cat /proc/sys/kernel/core_pattern)" = "core" ]; then
	echo "If this prompts you for sudo access, it's because your system is set up to send core dumps to apport instead of the parent process"
	echo "See https://stackoverflow.com/questions/35441062/afl-fuzzing-without-root-avoid-modifying-proc-sys-kernel-core-pattern#35470012 if you want more details"
	echo "If you don't want to run sudo from strange scripts, run the following command and you won't be prompted again"
	echo "sudo sh -c 'echo \"core\" > /proc/sys/kernel/core_pattern'"
	sudo sh -c 'echo "core" > /proc/sys/kernel/core_pattern'
fi

RUSTFLAGS="-Clink-arg=-fuse-ld=gold" cargo afl build --bin afl
AFL_SKIP_CPUFREQ=1 timeout 120 cargo afl fuzz -i afl/inputs -o afl/outputs target/debug/afl || true
cat afl/outputs/crashes/* afl/outputs/hangs/* || true
