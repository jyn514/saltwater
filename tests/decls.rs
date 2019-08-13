mod utils;

#[test]
fn test_decl_and_func_definition() {
    utils::assert_compile_error("int i, main(void) { return 0; }");
    utils::assert_compile_error("int main(void) { return 0; }, i;");
    utils::assert_succeeds("int f(), i; int main(void) { return 0; }");
}

#[test]
fn test_initializers() {
    utils::assert_compile_error("char c = '🙃';");
    utils::assert_compile_error("int a[-1];");
    utils::assert_succeeds(
        "
    int i = 1;
    int a[3] = {1, 2, 3};
    int b[2][2] = {{1, 2}, {3, 4}};
    double d = 1.2;
    float f = 1.2;
    char c = 'h';
    char s[] = \"hi there\";
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
