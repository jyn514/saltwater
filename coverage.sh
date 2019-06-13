cargo test --no-run
rm target/debug/compiler-*.d
kcov --verify target/cov target/debug/compiler-*
xdg-open target/cov/index.html
