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
