mod utils;

#[test]
fn return_type() {
    utils::assert_compile_error("int main(void) { return; }");
    utils::assert_compile_error(
        "void f() { return 1; }
         int main(void) { return 0; }",
    );
    utils::assert_compile_error("int f() {}");
    assert_eq!(
        utils::compile_and_run("int main(void) { return 1.1; }".to_string(), &[])
            .unwrap()
            .status
            .code(),
        Some(1)
    );
}

#[test]
fn branch_return() {
    utils::assert_code(
        "int main() {
    if (1) {
        return 1;
    }
}",
        1,
    );
    utils::assert_succeeds(
        "int main() {
    if (0) {
        return 1;
    }
}",
    );
    utils::assert_compile_error(
        "int main() {
    if (1) { return 1; } else { return 0; }
    return 2;
}",
    );
    utils::assert_compile_error("int f() {}");
    utils::assert_compile_error(
        "int f() {
    if (0) { return 0; }
}",
    );
}

#[test]
fn main_is_special() {
    utils::assert_succeeds("int main() {}");
}
