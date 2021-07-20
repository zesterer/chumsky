/// A utility type to allow chaining parser outputs together.
pub trait Chain<T> {
    /// The number of items that this chain link consists of.
    fn len(&self) -> usize;

    /// Append the elements in this link to the chain.
    fn append(self, v: &mut Vec<T>);

    /// Returns `true` if `self` has a length of zero items
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T> Chain<T> for T {
    fn len(&self) -> usize {
        1
    }

    fn append(self, v: &mut Vec<Self>) {
        v.push(self);
    }
}

impl<T> Chain<T> for Option<T> {
    fn len(&self) -> usize {
        self.is_some() as usize
    }

    fn append(self, v: &mut Vec<T>) {
        if let Some(x) = self {
            v.push(x);
        }
    }
}

impl<T> Chain<T> for Vec<T> {
    fn len(&self) -> usize {
        self.as_slice().len()
    }

    fn append(mut self, v: &mut Self) {
        v.append(&mut self);
    }
}
