#![allow(dead_code)]

/// Key error enumeration.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum KeyErr {
    /// Zero key usage.
    ZeroLen,
    /// Unknown key usage.
    Unknown,
}

/// Insert result type.
pub type InsRes<'a, T> = (&'a mut T, Option<T>);

/// Auxiliary trait for working with [`InsRes`].
pub trait InsResAide<T> {
    /// Returns `true` if [`InsRes`] holds previous record.
    fn previous(&self) -> bool;
    /// Returns `T` of [`InsRes`] `Some(T)` and _panics_ if [`None`].
    fn uproot_previous(&mut self) -> T;
    /// Returns `T` of [`InsRes`] `Some(T)` and produces _undefined behavior_ if [`None`].
    fn uproot_unchecked_previous(&mut self) -> T;
}

impl<'a, T> InsResAide<T> for InsRes<'a, T> {
    /// Returns `true` if [`InsRes`] holds previous record.
    fn previous(&self) -> bool {
        self.1.is_some()
    }

    /// Returns `T` of [`InsRes`] `Some(T)` leaving [`None`] in its place.
    ///
    ///_Panics_ if [`None`].
    fn uproot_previous(&mut self) -> T {
        if let Some(p) = self.1.take() {
            return p;
        } else {
            panic!("InsRes previous entry was `None`");
        }
    }

    /// Returns `T` of [`InsRes`] `Some(T)` leaving [`None`] in its place.     
    ///
    /// Produces _undefined behavior_ if [`None`].    
    ///
    /// Check with [`std::hint::unreachable_unchecked`] for more information.    
    fn uproot_unchecked_previous(&mut self) -> T {
        // SAFETY: the safety contract must be upheld by the caller.
        unsafe { self.1.take().unwrap_unchecked() }
    }
}

#[cfg(test)]
mod tests_of_units {

    mod ins_res {
        use super::super::{InsRes, InsResAide};

        #[test]
        fn previous() {
            let mut ins_res: InsRes<'_, usize> = (&mut 3, None);
            assert_eq!(false, ins_res.previous());

            ins_res.1 = Some(4);
            assert_eq!(true, ins_res.previous());
        }

        #[test]
        fn uproot_previous_ok() {
            let mut ins_res: InsRes<'_, usize> = (&mut 3, Some(4));
            assert_eq!(4, ins_res.uproot_previous());
        }

        #[test]
        #[should_panic(expected = "InsRes previous entry was `None`")]
        fn uproot_previous_nok() {
            let mut ins_res: InsRes<'_, usize> = (&mut 3, None);
            _ = ins_res.uproot_previous();
        }

        #[test]
        fn uproot_unchecked_previous_ok() {
            let mut ins_res: InsRes<'_, usize> = (&mut 3, Some(4));
            assert_eq!(4, ins_res.uproot_unchecked_previous());
        }
    }
}

// cargo fmt && cargo test --release
