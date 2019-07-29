mod utils;

#[test]
fn return_type() {
    utils::assert_compile_error("int main(void) { return; }".to_string());
    utils::assert_compile_error(
        "void f() { return 1; }
         int main(void) { return 0; }"
            .to_string(),
    );
    utils::assert_compile_error("int main(void) { return 1.1; }".to_string());
}
