mod utils;

#[test]
fn add() {
    utils::assert_succeeds("int main() { return 0 + 0; }");
    utils::assert_code("int main() { return 1 + 1; }", 2);
    utils::assert_code("int main() { return 1 + 2 + 3; }", 6);
    utils::assert_code("int main() { return 1.6 + 2.5; }", 4);
}

#[test]
fn sub() {
    utils::assert_code("int main() { return 0 - 0; }", 0);
    utils::assert_code("int main() { return 3 - 1; }", 2);
    utils::assert_code("int main() { return 10 - (1 - 2); }", 11);
    utils::assert_code("int main() { return 6.1 - 3.2; }", 2);
}

#[test]
fn mul() {
    utils::assert_code("int main() { return 1 * 10; }", 10);
    utils::assert_code("int main() { return 1 * 0; }", 0);
    utils::assert_code("int main() { return 3 * 4 * 5; }", 60);
    utils::assert_code("int main() { return 2.3 * 2.1; }", 4);
}

#[test]
fn div() {
    utils::assert_code("int main() { return 10 / 2; }", 5);
    utils::assert_code("int main() { return 0 / 1; }", 0);
    utils::assert_code("int main() { return 4 / 3; }", 1);
    utils::assert_code("int main() { return 3.1 / 3.0; }", 1);
}
