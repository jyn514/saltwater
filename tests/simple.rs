mod utils;

use utils::compile_and_run as run;

#[test]
fn no_op() {
    assert!(dbg!(
        run("int main(void) { return 0; }".to_string(), &[])
            .expect("compilation should succeed")
            .status
    )
    .success());
}

#[test]
fn exit_status() {
    assert!(
        run("int main(void) { return 1; }".to_string(), &[])
            .expect("compilation should succeed")
            .status
            .code()
            == Some(1)
    );
}
