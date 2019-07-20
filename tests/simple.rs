mod utils;

use utils::compile_program;

#[test]
fn main_return() {
    compile_program("int main(void) { return 0; }".to_string());
}
