use crate::data::Type;

impl Type {
    pub fn can_represent(&self, other: &Type) -> bool {
        unimplemented!(
            "don't know if {} can represent {}, it's platform dependent",
            self,
            other
        )
    }
    pub fn sizeof(&self) -> usize {
        unimplemented!("sizeof is inherently platform dependent")
    }
}
