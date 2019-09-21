mod utils;

#[test]
fn extern_call() {
    utils::assert_output(
        "
int putchar(char);
int main(void) {
    putchar('a');
}",
        "a",
    );
}

#[test]
fn intern_call() {
    utils::assert_code(
        "
int f() {
    return 1;
}
int main() {
    return f();
}",
        1,
    );
}

#[test]
fn declaration_before_definition() {
    utils::assert_succeeds(
        "int f();
int f() { return 0; }
int main() { return f(); }",
    )
}

#[test]
fn no_prototype() {
    utils::assert_succeeds(
        "
    void f() {}
    int main() {
        f(1);
    }",
    );
}

#[test]
fn func_pointers() {
    utils::assert_code(
        "
int (*func)();
int f() { return 1; }
int main() {
    func = &f;
    return (*func)();
}",
        1,
    );
    utils::assert_code(
        "
int f() { return 1; }
int main() {
    int (*func)() = f;
    return (*func)();
}",
        1,
    );
    utils::assert_code(
        "int f(), (*fp)() = f;
    int main() {
            return fp();
    }
    int f() { return 1; }",
        1,
    );
}
