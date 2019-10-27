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
    utils::assert_code(include_str!("../examples/readme.c"), 6)
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
    utils::assert_succeeds(
        "int main() {
        int i = 1;
        while (i) --i;
    }",
    );
}

#[test]
fn pointer_cast() {
    utils::assert_succeeds(
        "int main() {
    int *p;
    while (p);
    }",
    );
}

#[test]
#[ignore] // waiting on https://github.com/jyn514/rcc/issues/92
fn strlen() {
    utils::assert_code(
        "
    typedef unsigned long size_t;
    size_t strlen(char *str) {
        size_t len = 0;
        while (*str++) ++len;
        return len;
    }
    int main() { return strlen(\"hi\"); }",
        2,
    );
}

#[test]
fn do_loop() {
    utils::assert_code(
        "int main() {
    int i = 0;
    do {
            i += 1;
    } while (i < 5);
    return i;
        }",
        5,
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
    utils::assert_succeeds(
        "typedef int DWORD;
    int main() {
        for (DWORD i = 1; i > 0; --i);
    }",
    );
    utils::assert_output(
        "int putchar(int c);
        int main() {
            for (int i = 0; i < 3; ++i) putchar('a');
            for (int i = 0; i < 3; ++i) putchar('a');
        }",
        "aaaaaa",
    );
}

#[test]
fn switch() {
    utils::assert_code(
        "int i = 1;
    int main() {
        switch(i) {
            case 1: return 1;
        }
    }",
        1,
    );
    utils::assert_code(
        "int i = 1;
    int main() {
        switch(i) {
            default: return 1;
        }
    }",
        1,
    );
    utils::assert_code(
        "int i = 1;
    int main() {
        switch(i) {
            case 1:
            case 2:
            default: return 1;
        }
    }",
        1,
    );
    utils::assert_code(
        "int i = 1;
    int main() {
        switch(i) {
            case 2: return 2;
        }
    }",
        0,
    );
    utils::assert_code(
        "int i = 1;
    int main() {
        switch(i) {
            case 1: break;
            case 2: return 2;
        }
    }",
        0,
    );
    utils::assert_code(
        "
int prime(void);
void process_prime(), process_composite();
int x = 3;
int main() {
    switch(x)
      default:
        if (prime())
          case 2: case 3: case 5: case 7:
            return 1;
        else
          case 4: case 6: case 8: case 9: case 10:
            return 2;
}
int prime() { return 1; }",
        1,
    );
    utils::assert_succeeds(
        "int a;
void print_one(), print_two(), print_three(), print_dunno();
int main() {
    switch(a) {
        case 1: print_one();
        case 2: print_two();
        case 3: print_three();
        default: print_dunno();
    }
}
void print_one() {}
void print_two() {}
void print_three() {}
void print_dunno() {}
",
    );
}

#[test]
#[ignore]
fn goto() {
    utils::assert_succeeds(
        "int main() {
    start:
        if (0) goto start;
    }",
    );
    utils::assert_succeeds(
        "
    int main() {
        int x = 0;
        if (0) goto fail;
        if (1) goto succeed;
        goto fail;

        succeed: return 0;
        fail: return 1;
    }",
    );
}
