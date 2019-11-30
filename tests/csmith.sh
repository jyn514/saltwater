#!/bin/sh
set -euv
ROOT="$(git rev-parse --show-toplevel)"
csmith | "$ROOT/mycpp" -I$CSMITH_HOME/runtime | cargo run
