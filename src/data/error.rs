use super::Locatable;

pub type CompileError = Locatable<String>;
pub type SemanticResult<T> = Result<T, CompileError>;
