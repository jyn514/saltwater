mod utils;

#[test]
fn test_decl_and_func_definition() {
    utils::assert_compile_error("int i, main(void) { return 0; }");
    utils::assert_compile_error("int main(void) { return 0; }, i;");
    utils::assert_succeeds("int f(), i; int main(void) { return 0; }");
}

#[test]
fn test_decl_after_init() {
    utils::assert_succeeds("int main(); int main() {} int main();");
}

#[test]
fn test_different_types() {
    utils::assert_compile_error("int i; long i;");
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
    short s = 31;
    unsigned u = -1;
    char c = 'h';
    char h[] = \"hi there\";
    int main(void) { return 0; }
    ",
    );
}

#[test]
fn abstract_param_in_definition() {
    utils::assert_compile_error("int f(int) { return 1; }");
}

#[test]
fn bad_signature_for_main() {
    utils::assert_compile_error("int main(int);");
    utils::assert_compile_error("int main(char **);");
    utils::assert_compile_error("int main(int, char **, ...);");
    utils::assert_succeeds("int main(int argc, char ** argv) {}");
    utils::assert_succeeds("int main(int argc, char *argv[]) {}");
    // TODO: check char main[] is valid
}

#[test]
fn declare_local() {
    utils::assert_succeeds(
        "int main(void) {
    int i = 0;
    return i;
}",
    );
}

#[test]
fn declare_local_function() {
    utils::assert_code(
        "
int main() {
    int f();
    return f();
}

int f() { return 1; }",
        1,
    );
}

#[test]
#[should_panic(expected = "not yet implemented: data declarations")]
fn declare_global() {
    utils::not_implemented("int x; int main() { return x; }");
}

/* will fail until I add scoping
#[test]
fn local_function_goes_out_of_scope() {
    utils::assert_compile_error(
        "
int main() {
    int f();
}

int g() {
    return f();
}",
    );
}
*/
