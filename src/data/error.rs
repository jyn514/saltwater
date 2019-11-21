use super::Locatable;

pub type CompileError = Locatable<String>;
pub type CompileResult<T> = Result<T, CompileError>;
