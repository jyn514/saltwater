mod utils;

use utils::compile_and_run as run;

#[test]
fn main_return() {
    assert!(run("int main(void) { return 0; }".to_string(), &[])
        .expect("compilation should succeed")
        .status
        .success())
}
