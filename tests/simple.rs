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
    for i in 0..255 {
        assert!(
            run(format!("int main(void) {{ return {}; }}", i), &[])
                .expect("compilation should succeed")
                .status
                .code()
                == Some(i)
        );
    }
}
