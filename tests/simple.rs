mod utils;

use utils::compile_and_run as run;

#[test]
fn no_op() {
    assert!(dbg!(
        run("int main(void) { return 0; }", &[])
            .expect("compilation should succeed")
            .status
    )
    .success());
}

#[test]
fn exit_status() {
    assert!(
        run("int main(void) { return 1; }", &[])
            .expect("compilation should succeed")
            .status
            .code()
            == Some(1)
    );
}

#[test]
fn empty_decl_does_not_stop_parsing() {
    assert!(run("int; int main(void) { return 0; }", &[])
        .expect("compilation should succeed")
        .status
        .success());
}

#[test]
fn empty_program_is_err() {
    utils::assert_compile_error("");
}

#[test]
fn only_bad_tokens_are_error() {
    utils::assert_compile_error("`");
    utils::assert_compile_error("`int main(){}");
}

#[test]
fn multiple_errors() {
    utils::assert_num_errs("int f(int) { return; }", 2);
    utils::assert_num_errs("int int enum e;", 2);
}
