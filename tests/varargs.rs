mod utils;

extern crate env_logger;
extern crate log;

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
    use log::info;
    use std::process::Command;

    let mut replaced = vec![];
    let new_args = args.iter().enumerate().map(|(i, arg)| {
        // replace 'a' with a
        if arg.len() == 3 && arg.chars().nth(0) == Some('\'') && arg.chars().nth(2) == Some('\'') {
            replaced.push(i);
            &arg[1..2]
        } else {
            arg
        }
    });
    let mut all_args: Vec<_> = std::iter::once(format).chain(new_args).collect();
    let expected = Command::new("printf")
        .args(&all_args)
        .output()
        .expect("printf is not installed or syntax is incorrect");
    info!(
        "system printf thinks {:?} should be {:?}",
        all_args, expected
    );

    let quoted = format!("\"{}\"", all_args[0]);
    all_args[0] = &quoted;
    for i in replaced {
        all_args[i + 1] = args[i];
    }
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
    env_logger::builder().is_test(true).init();
    printf_helper(r"exit_success: %d\n", &["5"]);
    printf_helper(r"exit_success: %ld\n", &["5000000l"]);
    printf_helper(r"exit_success: %c\n", &["'a'"]);
}

#[test]
fn multiple_given_args() {
    utils::assert_output(
        "int sprintf(char *str, const char *format, ...);
        int puts(const char *s);
        int main() {
            char buf[100];
            sprintf(buf, \"it is %d\\n\", 2019);
            puts(buf);
        }",
        "it is 2019\n\n",
    );
}
