extern crate compiler;

pub fn compile_program(program: String) {
    compiler::compile(program, "<integration-test>".to_string(), false);
}
