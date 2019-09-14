use std::ops::Index;

use crate::data::Type;

#[derive(Debug, Default)]
pub struct Types(Vec<Type>);
pub type TypeIndex = usize;

impl Types {
    pub fn get_or_insert(&mut self, ctype: Type) -> usize {
        // TODO: this is grossly inefficient
        if let Some(index) = self
            .0
            .iter()
            .position(|current| current.strong_eq(&ctype, self))
        {
            index
        } else {
            self.0.push(ctype);
            self.0.len()
        }
    }
    pub(crate) fn eq(&self, x: usize, y: usize) -> bool {
        x == y || self[x] == self[y]
    }
}

// Note that IndexMut is not implemented for Types,
// you aren't allowed to modify them once they're stored
impl Index<usize> for Types {
    type Output = Type;
    #[inline(always)]
    fn index(&self, index: usize) -> &Type {
        &self.0[index]
    }
}

impl Index<&usize> for Types {
    type Output = Type;
    #[inline(always)]
    fn index(&self, index: &usize) -> &Type {
        &self.0[*index]
    }
}
