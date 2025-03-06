use std::{cell::UnsafeCell, ops::Deref};

pub struct UC<T>(UnsafeCell<T>);

impl<T> UC<T> {
    pub fn get_ref(&self) -> &T {
        let t = self.0.get();
        unsafe { t.as_mut().unwrap_unchecked() }
    }

    pub fn get_mut(&self) -> &mut T {
        let t = self.0.get();
        unsafe { t.as_mut().unwrap_unchecked() }
    }

    pub const fn new(t: T) -> Self {
        Self(UnsafeCell::new(t))
    }
}

impl<T> Deref for UC<T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.get_ref()
    }
}

#[cfg(test)]
mod tests_of_units {
    use std::ops::Deref;

    use crate::UC;

    #[test]
    fn get_ref() {
        let zero = &0usize as *const usize;
        let uc = UC::new(zero);
        let test = uc.get_ref();

        assert_eq!(zero as usize, *test as usize);
    }

    #[test]
    fn get_mut() {
        let zero = &0usize as *const usize;
        let uc = UC::new(zero);
        let test = uc.get_mut();

        assert_eq!(zero as usize, *test as usize);
    }

    #[test]
    fn new() {
        let uc = UC::new(333);
        let mut test = uc.0;
        assert_eq!(333, *test.get_mut());
    }

    #[test]
    fn deref() {
        let uc = UC::new(11);
        assert_eq!(uc.get_ref(), uc.deref());
    }
}

// cargo test --release
