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
    utils::assert_succeeds("int g(int); int g(int i) { return i; } int main() { return g(0); }")
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
fn multiple_initializers() {
    utils::assert_code(
        "int main() {
        int i = 1, *p = &i;
        return *p;
}",
        1,
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
fn infer_array_bounds() {
    utils::assert_succeeds("int a[] = {1, 2, 3}; int main(){}");
    utils::assert_compile_error("int a[][] = {{1}};");
    utils::assert_succeeds("int a[][3] = {{1, 2, 3}}; int main(){}");
    utils::assert_compile_error("int a[][1] = {{1, 2, 3}}; int main(){}");
}

#[test]
fn declare_global() {
    utils::assert_succeeds("int x; int main() { return x; }");
}

#[test]
fn typedef() {
    utils::assert_succeeds(
        "
    typedef int i;
    i main() {}
",
    );
    utils::assert_code(
        "typedef int DWORD, INT, *INT_POINTER;
    INT main() {
        DWORD i = 1;
        INT_POINTER p = &i;
        return *p;
    }",
        1,
    );
    utils::assert_code(
        "typedef int INT; typedef INT i;
         i main() { return 1; }",
        1,
    );
    utils::assert_succeeds(
        "int main() {
    typedef void v;
}",
    );
}

#[test]
fn struct_and_enum() {
    utils::assert_compile_error("enum e;");
    utils::assert_compile_error("enum;");
    utils::assert_compile_error("union;");
    utils::assert_compile_error("struct;");
}

#[test]
fn function() {
    utils::assert_code(
        "
        int f(int i) { return i; }
        int main() { return f(1); }
    ",
        1,
    );
    utils::assert_code(
        "
        int f(double d) { return d + .5; }
        int main() { return f(1.2); }
    ",
        1,
    );
    utils::assert_code(
        "
        int f(char c) { return c + .5; }
        int main(void) { return f(1.2); }
    ",
        1,
    );
}

#[test]
fn forward_declaration_with_typedef() {
    utils::assert_succeeds(
        "
    typedef struct s *sp;
    struct s { int i; } my_s;
    int main() {
        sp my_p = &my_s;
        return my_p->i = 0;
    }",
    );
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
