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
///
/// Check with implementations for details.
pub trait InsResAide<T> {
    /// Checks whether [`InsRes`] holds previous record.
    fn previous(&self) -> bool;
    /// Uproots `T` of [`InsRes`] `Some(T)`.
    fn uproot_previous(&mut self) -> T;
    /// Uproots `T` of [`InsRes`] `Some(T)` in unsafe manner.
    unsafe fn uproot_previous_unchecked(&mut self) -> T;
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
    unsafe fn uproot_previous_unchecked(&mut self) -> T {
        // SAFETY: the safety contract must be upheld by the caller.
        self.1.take().unwrap_unchecked()
    }
}

impl<'a, T> InsResAide<T> for Result<InsRes<'a, T>, KeyErr> {
    /// Wraps call to [`InsResAide::previous`] of [`InsRes`].
    ///
    ///_Panics_ if [`Err`].
    fn previous(&self) -> bool {
        return if let Ok(r) = self.as_ref() {
            r.previous()
        } else {
            panic!("`Err` variant was supplied.");
        };
    }

    /// Wraps call to [`InsResAide::uproot_previous`] of [`InsRes`].
    ///
    ///_Panics_ if [`Err`].
    fn uproot_previous(&mut self) -> T {
        return if let Ok(r) = self.as_mut() {
            r.uproot_previous()
        } else {
            panic!("`Err` variant was supplied.");
        };
    }

    /// Wraps call to [`InsResAide::uproot_previous_unchecked`] of [`InsRes`].
    ///
    ///_Panics_ if [`Err`].
    ///
    /// In moderation, hybridized method as in fact [`Result`] is checked. Only [`InsRes`] is _'unchecked'_.    
    unsafe fn uproot_previous_unchecked(&mut self) -> T {
        return if let Ok(r) = self.as_mut() {
            r.uproot_previous_unchecked()
        } else {
            panic!("`Err` variant was supplied.");
        };
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
        fn uproot_previous_unchecked_ok() {
            let mut ins_res: InsRes<'_, usize> = (&mut 3, Some(4));
            assert_eq!(4, unsafe { ins_res.uproot_previous_unchecked() });
        }
    }

    mod result_ins_res_key_err {
        use super::super::{InsRes, InsResAide, KeyErr};

        #[test]
        fn previous_ok() {
            let ins_res = (&mut 3, Some(4));
            let res = Ok(ins_res);
            assert_eq!(true, res.previous());
        }

        #[test]
        #[should_panic(expected = "`Err` variant was supplied.")]
        fn previous_err() {
            let res: Result<InsRes<usize>, KeyErr> = Err(KeyErr::ZeroLen);
            _ = res.previous();
        }

        #[test]
        fn uproot_previous_ok() {
            let ins_res = (&mut 3, Some(4));
            let mut res = Ok(ins_res);
            assert_eq!(4, res.uproot_previous());
        }

        #[test]
        #[should_panic(expected = "`Err` variant was supplied.")]
        fn uproot_previous_err() {
            let mut res: Result<InsRes<usize>, KeyErr> = Err(KeyErr::ZeroLen);
            _ = res.uproot_previous();
        }

        #[test]
        fn uproot_previous_unchecked_ok() {
            let ins_res = (&mut 3, Some(4));
            let mut res = Ok(ins_res);
            assert_eq!(4, unsafe { res.uproot_previous_unchecked() });
        }

        #[test]
        #[should_panic(expected = "`Err` variant was supplied.")]
        fn uproot_previous_unchecked_err() {
            let mut res: Result<InsRes<usize>, KeyErr> = Err(KeyErr::ZeroLen);
            _ = unsafe { res.uproot_previous_unchecked() };
        }
    }
}

// cargo fmt && cargo test --release
