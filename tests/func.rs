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
