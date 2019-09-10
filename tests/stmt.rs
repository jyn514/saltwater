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

#[test]
fn readme_example() {
    utils::assert_code(
        "
int i = 1;
int a[3] = {1, 2, 3};
float f = 2.5;

int main(void) {
  const int c = 4;
  // should return 6
  return i + f*a[2] - c/a[1];
}",
        6,
    )
}

#[test]
fn scope() {
    utils::assert_compile_error(
        "
    int f(int i) {
        int i = 2;
        return i;
    }",
    );
    utils::assert_compile_error(
        "
    int f(int i) {
        int i = 2;
        int i = 2;
        return i;
    }",
    );
    utils::assert_code(
        "int i = 1;
    int main() {
        int i = 2;
        return i;
    }",
        2,
    );
    utils::assert_code(
        "int main() {
    int i = 2;
    {
        int i = 3;
        return i;
    }
}",
        3,
    );
}

#[test]
fn void() {
    utils::assert_succeeds(
        "int puts(const char *);
    void f() {
        puts(\"hi\");
    }
    int main() {
        f();
    }",
    );
}
