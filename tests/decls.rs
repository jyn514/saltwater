mod utils;

#[test]
fn test_decl_and_func_definition() {
    utils::assert_compile_error("int i, main(void) { return 0; }");
    utils::assert_compile_error("int main(void) { return 0; }, i;");
    utils::assert_succeeds("int f(), i; int main(void) { return 0; }");
}

#[test]
fn test_initializers() {
    utils::assert_succeeds(
        "
    int a[3] = {1, 2, 3};
    int main(void) { return 0; }
    ",
    );
}

#[test]
fn test_declare_local() {
    utils::assert_succeeds(
        "int main(void) {
    int i = 0;
    return i;
}",
    );
}

#[test]
fn test_declare_local_function() {
    utils::assert_succeeds(
        "
int main() {
    int f();
    return f();
}",
    );
}

#[test]
fn test_local_function_goes_out_of_scope() {
    utils::assert_compile_error(
        "
int main() {
    int f();
    return f();
}

int g() {
    return f();
}",
    );
}
