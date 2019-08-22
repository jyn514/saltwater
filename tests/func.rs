mod utils;

#[test]
fn putc_extern() {
    utils::assert_output(
        "
int putchar(char);
int main(void) {
    putchar('a');
}",
        "a",
    );
}
