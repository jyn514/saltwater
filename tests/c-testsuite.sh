#!/bin/sh

set -ev

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT/tests"

[ -d c-testsuite ] || git clone https://github.com/c-testsuite/c-testsuite
cd c-testsuite

cargo build --release
TARGET="${CARGO_TARGET_DIR:-$ROOT/target}"

cat > runners/single-exec/rcc << EOF
#!/bin/sh

set -eu

CC="$TARGET/release/rcc"
CFLAGS=""

export CC CFLAGS
exec ./runners/single-exec/posix \$1
EOF

chmod +x runners/single-exec/rcc
./single-exec rcc | scripts/tapsummary
