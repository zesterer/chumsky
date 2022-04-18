//! Data structures to more efficiently aggregate the results of multiple parsers.

use std::{
    collections::LinkedList,
    iter::{FromIterator, FusedIterator},
};

/// Segmented list that internally stores sequences of multiple `T`s as they are added.
///
/// Addition of elements and element sequences behaves like a linked list and is O(1).
/// Using [`iter`](FlatList::iter), you can iterate over all elements as if they were stored in one, contiguous list.
#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct FlatList<T> {
    inner: LinkedList<Vec<T>>,
}

impl<T> Default for FlatList<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> FlatList<T> {
    /// Constructs a new, empty `FlatList<T>`.
    pub const fn new() -> Self {
        Self {
            inner: LinkedList::new(),
        }
    }

    /// Adds a single element to `self`.
    #[inline(always)]
    pub fn push(&mut self, t: T) {
        if self.inner.is_empty() {
            self.inner.push_back(Vec::with_capacity(8));
        }
        unsafe { self.inner.back_mut().unwrap_unchecked().push(t) };
    }

    /// Adds a sequence of `T`s to the list.
    #[inline(always)]
    pub fn add_sequence(&mut self, seq: Vec<T>) {
        if seq.is_empty() {
            return;
        }
        self.inner.push_back(seq);
    }

    /// Moves all the elements of `other` to the end of `self`, leaving `other` empty.
    ///
    /// This operation should compute in O(1) time and O(1) memory.
    #[inline(always)]
    pub fn append(&mut self, other: &mut FlatList<T>) {
        self.inner.append(&mut other.inner);
    }

    /// Returns the last element in the list, or `None` if the list is empty.
    #[inline(always)]
    pub fn last(&self) -> Option<&T> {
        // Note: `inner` cannot contain empty sequences, so the last sequence always contains at least one element
        self.inner.back().and_then(|seq| seq.last())
    }

    /// Returns a mutable reference the last element in the list, or `None` if the list is empty.
    #[inline(always)]
    pub fn last_mut(&mut self) -> Option<&mut T> {
        // Note: `inner` cannot contain empty sequences, so the last sequence always contains at least one element
        self.inner.back_mut().and_then(|seq| seq.last_mut())
    }

    /// Returns the number of elements in the list.
    pub fn len(&self) -> usize {
        self.inner.iter().map(|seq| seq.len()).sum()
    }

    /// Returns `true` if the list contains no elements.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty() || self.len() == 0
    }

    /// Returns an immutable iterator over all elements in `self`.
    #[inline(always)]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter::new(self)
    }
}

impl<'list, T: 'list> IntoIterator for &'list FlatList<T> {
    type Item = &'list T;
    type IntoIter = Iter<'list, T>;

    /// Returns an immutable iterator over all elements in `self`.
    #[inline(always)]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T> IntoIterator for FlatList<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    /// Returns an owned iterator over all elements in `self`.
    #[inline(always)]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self)
    }
}

impl<T> Extend<T> for FlatList<T> {
    #[cfg(feature = "nightly")]
    #[inline(always)]
    fn extend_one(&mut self, item: T) {
        self.push(item);
    }

    #[inline(always)]
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.add_sequence(iter.into_iter().collect())
    }
}

impl<T> FromIterator<T> for FlatList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut this = Self::new();
        this.extend(iter);
        this
    }
}

/// Immutable flat list iterator.
/// Will iterate over the flat list as a single sequence of `T`s.
#[derive(Debug)]
pub struct Iter<'list, T: 'list> {
    list_iter: std::collections::linked_list::Iter<'list, Vec<T>>,
    current_segment: Option<std::slice::Iter<'list, T>>,
    done: bool,
}

impl<'list, T: 'list> Iter<'list, T> {
    fn new(list: &'list FlatList<T>) -> Self {
        // make sure that if we start with the first segment of `inner` already the list iterator is advanced and we don't get that segment twice
        let mut list_iter = list.inner.iter();
        let mut done = false;
        let current_segment = match list_iter.next().map(|v| v.iter()) {
            iter @ Some(_) => iter,
            None => {
                done = true;
                None
            }
        };
        Self {
            list_iter,
            current_segment,
            done,
        }
    }
}

impl<'list, T: 'list> Iterator for Iter<'list, T> {
    type Item = &'list T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        loop {
            if let Some(seq) = self.current_segment.as_mut() {
                match seq.next() {
                    Some(elem) => return Some(elem),
                    None => match self.list_iter.next() {
                        // N.B. `LinkedList`'s `Iter` is a `FusedIterator`
                        Some(seq) => self.current_segment = Some(seq.iter()),
                        None => {
                            self.done = true;
                            return None;
                        }
                    },
                }
            }
        }
    }
}

impl<'list, T: 'list> FusedIterator for Iter<'list, T> {}

/// Owned flat list iterator.
/// Will iterate over the flat list as a single sequence of `T`s.
#[derive(Debug)]
pub struct IntoIter<T> {
    list_iter: std::collections::linked_list::IntoIter<Vec<T>>,
    current_segment: Option<std::vec::IntoIter<T>>,
    done: bool,
}

impl<T> IntoIter<T> {
    fn new(list: FlatList<T>) -> Self {
        // make sure that if we start with the first segment of `inner` already the list iterator is advanced and we don't get that segment twice
        let mut list_iter = list.inner.into_iter();
        let mut done = false;
        let current_segment = match list_iter.next().map(|v| v.into_iter()) {
            iter @ Some(_) => iter,
            None => {
                done = true;
                None
            }
        };
        Self {
            list_iter,
            current_segment,
            done,
        }
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        loop {
            if let Some(seq) = self.current_segment.as_mut() {
                match seq.next() {
                    Some(elem) => return Some(elem),
                    None => match self.list_iter.next() {
                        // N.B. `LinkedList`'s `IntoIter` is a `FusedIterator`
                        Some(seq) => self.current_segment = Some(seq.into_iter()),
                        None => {
                            self.done = true;
                            return None;
                        }
                    },
                }
            }
        }
    }
}

impl<T> FusedIterator for IntoIter<T> {}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn iter() {
        let mut list = FlatList::new();
        list.add_sequence(vec![1, 2, 3, 4]);
        list.push(5);
        list.add_sequence(vec![6, 7]);
        list.push(8);
        list.push(9);
        let collected: Vec<_> = list.iter().copied().collect();
        let expected: Vec<_> = (1..=9).collect();
        assert_eq!(collected, expected);
    }

    #[test]
    fn iter_only_singles() {
        let mut list = FlatList::new();
        list.push(5);
        list.push(8);
        list.push(9);
        let collected: Vec<_> = list.iter().copied().collect();
        assert_eq!(collected, vec![5, 8, 9]);
    }

    #[test]
    fn iter_empty() {
        let list = FlatList::<usize>::new();
        let collected: Vec<_> = list.iter().copied().collect();
        assert_eq!(collected, vec![]);
    }

    #[test]
    fn into_iter() {
        let mut list = FlatList::new();
        list.add_sequence(vec![1, 2, 3, 4]);
        list.push(5);
        list.add_sequence(vec![6, 7]);
        list.push(8);
        list.push(9);
        let collected: Vec<_> = list.into_iter().collect();
        let expected: Vec<_> = (1..=9).collect();
        assert_eq!(collected, expected);
    }

    #[test]
    fn into_iter_only_singles() {
        let mut list = FlatList::new();
        list.push(5);
        list.push(8);
        list.push(9);
        let collected: Vec<_> = list.into_iter().collect();
        assert_eq!(collected, vec![5, 8, 9]);
    }

    #[test]
    fn into_iter_empty() {
        let list = FlatList::<usize>::new();
        let collected: Vec<_> = list.into_iter().collect();
        assert_eq!(collected, vec![]);
    }

    #[test]
    fn append() {
        let mut list = FlatList::new();
        list.add_sequence(vec![1, 2, 3, 4]);
        list.push(5);
        list.add_sequence(vec![6, 7]);
        list.push(8);
        list.push(9);
        let mut list2 = FlatList::new();
        list2.append(&mut list);
        let collected: Vec<_> = list2.into_iter().collect();
        let expected: Vec<_> = (1..=9).collect();
        assert_eq!(collected, expected);
        assert!(list.is_empty());
    }
}
