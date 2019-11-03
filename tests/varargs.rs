mod utils;

fn printf(args: &[&str], expected: &str) {
    let program = format!(
        "
    int printf(const char *format, ...);
    int main() {{
        printf({});
    }}",
        args.join(", ")
    );
    utils::assert_output(&program, expected);
}

fn printf_helper(format: &str, args: &[&str]) {
    use std::process::Command;
    let mut all_args = vec![format];
    all_args.extend_from_slice(args);
    let expected = Command::new("printf")
        .args(&all_args)
        .output()
        .expect("printf is not installed or syntax is incorrect");

    let quoted = format!("\"{}\"", all_args[0]);
    all_args[0] = &quoted;
    printf(
        &all_args,
        std::str::from_utf8(&expected.stdout).expect("output should be valid utf8"),
    );
}

#[test]
fn literals() {
    printf_helper(r"hello world\n", &[]);
    printf_helper("goodbye world", &[]);
}

#[test]
fn ints() {
    printf_helper(r"exit_success: %d\n", &["5"]);
    printf_helper(r"exit_success: %ld\n", &["5000000l"]);
    printf_helper(r"exit_success: %c\n", &["'5'"]);
}
