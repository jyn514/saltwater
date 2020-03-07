mod utils;

use rcc::{Opt, JIT};

#[test]
fn jit_readme() -> Result<(), Box<dyn std::error::Error>> {
    let _ = env_logger::try_init();
    let path = "tests/runner-tests/readme.c";
    let readme = std::fs::read_to_string(path)?;
    let (jit, _warnings) = JIT::from_string(readme, &Opt::default());
    let code = unsafe { jit?.run_main() };
    assert_eq!(code, Some(6));
    Ok(())
}
