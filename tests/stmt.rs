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
        typedef struct s *sp;

int i = 1;
int a[3] = {1, 2, 3};
float f = 2.5;

struct s {
  union {
    struct {
      char a, b, c, d;
    } s;
    int inner;
  } u;
  int outer;
} my_struct;

int g(int);

int main(void) {
  sp my_struct_pointer = &my_struct;
  const int c = my_struct_pointer->outer = 4;
  // should return 6
  return i + f*a[2] - c/g(1);
}

int g(int i) {
  if (i < 0 || i >= 3) {
    return 0;
  }
  return a[i];
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

#[test]
fn while_loop() {
    utils::assert_output(
        "
    int putchar(int);
    int main() {
        int i = 5;
        while (i >= 0) {
                putchar(i + 'a');
                i -= 1;
        }
    }",
        "fedcba",
    );
}

#[test]
fn for_loop() {
    utils::assert_output(
        "int putchar(char);
int main() {
        for (int i = 0; i < 10; i += 1) {
                putchar('a' + i);
        }
}
",
        "abcdefghij",
    );
}
