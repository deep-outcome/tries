#![allow(dead_code)]

/// Key error enumeration.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum KeyErr {
    /// Zero key usage.
    ZeroLen,
    /// Unknown key usage.
    Unknown,
}

impl<'a, T> From<InsRes<'a, T>> for KeyErr {
    /// Return value is `KeyError` if `InsRes::Err(_)`; _panics_ otherwise.
    fn from(ir: InsRes<T>) -> Self {
        if let InsRes::Err(keer) = ir {
            keer
        } else {
            panic!("Not InsRes::Err(_) variant.")
        }
    }
}

impl<'a, T> From<AcqRes<'a, T>> for KeyErr {
    /// Return value is `KeyError` if `AcqRes::Err(_)`; _panics_ otherwise.
    fn from(ar: AcqRes<T>) -> Self {
        if let AcqRes::Err(keer) = ar {
            keer
        } else {
            panic!("Not AcqRes::Err(_) variant.")
        }
    }
}

impl<'a, T> From<AcqMutRes<'a, T>> for KeyErr {
    /// Return value is `KeyError` if `AcqMutRes::Err(_)`; _panics_ otherwise.
    fn from(ar: AcqMutRes<T>) -> Self {
        if let AcqMutRes::Err(keer) = ar {
            keer
        } else {
            panic!("Not AcqMutRes::Err(_) variant.")
        }
    }
}

impl<T> From<RemRes<T>> for KeyErr {
    /// Return value is `KeyError` if `RemRes::Err(_)`; _panics_ otherwise.
    fn from(rr: RemRes<T>) -> Self {
        if let RemRes::Err(keer) = rr {
            keer
        } else {
            panic!("Not RemRes::Err(_) variant.")
        }
    }
}

/// Insertion result enumeration.
#[derive(Debug, PartialEq, Eq)]
pub enum InsRes<'a, T> {
    /// Insertion accomplished. Holds mutable reference to inserted
    /// entry and optionally previous entry, based on its existence.
    Ok((&'a mut T, Option<T>)),
    /// Key error.
    Err(KeyErr),
}

impl<'a, T> InsRes<'a, T> {
    /// Returns `true` if `InsRes::Ok(_)`, if not `false`.
    pub const fn is_ok(&self) -> bool {
        match self {
            InsRes::Ok(_) => true,
            _ => false,
        }
    }

    /// Returns `true` if `InsRes::Ok((_, Some(T)))`, if not `false`.
    pub const fn is_ok_some(&self) -> bool {
        if let InsRes::Ok(opt) = self {
            if let Some(_) = opt.1 {
                return true;
            }
        }

        false
    }

    /// Returns `(&mut T, Option<T>)` of `InsRes::Ok((&mut T, Option<T>))`
    /// or _panics_ if not that variant.
    pub fn uproot_ok(self) -> (&'a mut T, Option<T>) {
        if let InsRes::Ok(ok) = self {
            return ok;
        }

        panic!("Not InsRes::Ok(_) variant.")
    }

    /// Returns `T` of `InsRes::Ok((_, Some(T)))` or _panics_ if:
    /// - not that variant
    /// - `Option<T>` is `None`
    pub fn uproot_ok_some(self) -> T {
        if let InsRes::Ok(opt) = self {
            if let Some(t) = opt.1 {
                return t;
            }
        }

        panic!("Not InsRes::Ok(Some(T)) variant.")
    }

    /// Returns `(&mut T, Option<T>)` of `InsRes::Ok((&mut T, Option<T>))`
    /// and does not _panic_ (UB) if not that variant.
    ///
    /// Check with `std::hint::unreachable_unchecked` for more information.
    pub fn uproot_ok_unchecked(self) -> (&'a mut T, Option<T>) {
        if let InsRes::Ok(ok) = self {
            return ok;
        }

        // SAFETY: the safety contract must be upheld by the caller.
        unsafe { std::hint::unreachable_unchecked() }
    }

    /// Returns `T` of `InsRes::Ok((_, Some(T)))` and does not _panic_ (UB) if:
    /// - not that variant
    /// - `Option<T>` is `None`
    ///
    /// Check with `std::hint::unreachable_unchecked` for more information.
    pub unsafe fn uproot_ok_some_unchecked(self) -> T {
        if let InsRes::Ok(opt) = self {
            if let Some(t) = opt.1 {
                return t;
            }
        }

        // SAFETY: the safety contract must be upheld by the caller.
        unsafe { std::hint::unreachable_unchecked() }
    }
}

/// Acquisition result enumeration.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum AcqRes<'a, T> {
    /// Acquisition accomplished.
    Ok(&'a T),
    /// Key error.
    Err(KeyErr),
}

impl<'a, T> AcqRes<'a, T> {
    /// Returns `true` if `AcqRes::Ok(_)`, if not `false`.
    pub const fn is_ok(&self) -> bool {
        match self {
            AcqRes::Ok(_) => true,
            _ => false,
        }
    }

    /// Returns `&T` of `AcqRes::Ok(&T)` or _panics_ if not that variant.
    pub const fn uproot(&self) -> &T {
        match self {
            AcqRes::Ok(t) => t,
            _ => panic!("Not AcqRes::Ok(_) variant."),
        }
    }

    /// Returns `&T` of `AcqRes::Ok(&T)` and does not _panic_ if not that variant (UB).
    ///
    /// Check with `std::hint::unreachable_unchecked` for more information.
    pub const unsafe fn uproot_unchecked(&self) -> &T {
        match self {
            AcqRes::Ok(t) => t,
            // SAFETY: the safety contract must be upheld by the caller.
            _ => unsafe { std::hint::unreachable_unchecked() },
        }
    }
}

/// Acquisition result enumeration.
#[derive(Debug, PartialEq, Eq)]
pub enum AcqMutRes<'a, T> {
    /// Acquisition accomplished.
    Ok(&'a mut T),
    /// Key error.
    Err(KeyErr),
}

impl<'a, T> AcqMutRes<'a, T> {
    /// Returns `true` if `AcqMutRes::Ok(_)`, if not `false`.
    pub const fn is_ok(&self) -> bool {
        match self {
            AcqMutRes::Ok(_) => true,
            _ => false,
        }
    }

    /// Returns `&mut T` of `AcqMutRes::Ok(&mut T)` or _panics_ if not that variant.
    pub const fn uproot(&mut self) -> &mut T {
        match self {
            AcqMutRes::Ok(t) => t,
            _ => panic!("Not AcqMutRes::Ok(_) variant."),
        }
    }

    /// Returns `&mut T` of `AcqMutRes::Ok(&mut T)` and does not _panic_ if not that variant (UB).
    ///
    /// Check with `std::hint::unreachable_unchecked` for more information.
    pub const unsafe fn uproot_unchecked(&mut self) -> &mut T {
        match self {
            AcqMutRes::Ok(t) => t,
            // SAFETY: the safety contract must be upheld by the caller.
            _ => unsafe { std::hint::unreachable_unchecked() },
        }
    }
}

impl<T> Clone for RemRes<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        match self {
            Self::Ok(t) => Self::Ok(t.clone()),
            Self::Err(e) => Self::Err(e.clone()),
        }
    }
}

/// Removal result enumeration.
#[derive(Debug, PartialEq, Eq)]
pub enum RemRes<T> {
    /// Removal accomplished.
    Ok(T),
    /// Key error.
    Err(KeyErr),
}

impl<T> RemRes<T> {
    /// Returns `true` if `RemRes::Ok(_)`, if not `false`.
    pub const fn is_ok(&self) -> bool {
        match self {
            RemRes::Ok(_) => true,
            _ => false,
        }
    }

    /// Returns `T` of `RemRes::Ok(T)` or _panics_ if not that variant.
    pub fn uproot(self) -> T {
        match self {
            RemRes::Ok(t) => t,
            _ => panic!("Not RemRes::Ok(T) variant."),
        }
    }

    /// Returns `T` of `RemRes::Ok(T)` and does not _panic_ if not that variant (UB).
    ///
    /// Check with `std::hint::unreachable_unchecked` for more information.
    pub unsafe fn uproot_unchecked(self) -> T {
        match self {
            RemRes::Ok(t) => t,
            // SAFETY: the safety contract must be upheld by the caller.
            _ => unsafe { std::hint::unreachable_unchecked() },
        }
    }
}

#[cfg(test)]
mod tests_of_units {
    mod key_err {
        use super::super::{AcqMutRes, AcqRes, InsRes, KeyErr, RemRes};

        #[test]
        fn from_ins_res() {
            let from = From::from(InsRes::<usize>::Err(KeyErr::Unknown));
            assert_eq!(KeyErr::Unknown, from);
        }

        #[test]
        #[should_panic(expected = "Not InsRes::Err(_) variant.")]
        fn from_ins_res_panic() {
            let _: KeyErr = From::from(InsRes::<usize>::Ok((&mut 1, None)));
        }

        #[test]
        fn from_acq_res() {
            let from = From::from(AcqRes::<usize>::Err(KeyErr::Unknown));
            assert_eq!(KeyErr::Unknown, from);
        }

        #[test]
        #[should_panic(expected = "Not AcqRes::Err(_) variant.")]
        fn from_acq_res_panic() {
            let _: KeyErr = From::from(AcqRes::<usize>::Ok(&3));
        }

        #[test]
        fn from_acq_mut_res() {
            let from = From::from(AcqMutRes::<usize>::Err(KeyErr::Unknown));
            assert_eq!(KeyErr::Unknown, from);
        }

        #[test]
        #[should_panic(expected = "Not AcqMutRes::Err(_) variant.")]
        fn from_acq_mut_res_panic() {
            let _: KeyErr = From::from(AcqMutRes::<usize>::Ok(&mut 3));
        }

        #[test]
        fn from_rem_res() {
            let from = From::from(RemRes::<usize>::Err(KeyErr::Unknown));
            assert_eq!(KeyErr::Unknown, from);
        }

        #[test]
        #[should_panic(expected = "Not RemRes::Err(_) variant.")]
        fn from_rem_res_panic() {
            let _: KeyErr = From::from(RemRes::<usize>::Ok(3));
        }
    }

    mod ins_res {
        use super::super::{InsRes, KeyErr};

        #[test]
        fn is_ok() {
            assert_eq!(true, InsRes::<usize>::Ok((&mut 1, None)).is_ok());
            assert_eq!(false, InsRes::<usize>::Err(KeyErr::ZeroLen).is_ok());
        }

        #[test]
        fn is_ok_some_some() {
            assert_eq!(true, InsRes::Ok((&mut 1, Some(3))).is_ok_some());
        }

        #[test]
        fn is_ok_some_none() {
            assert_eq!(false, InsRes::<usize>::Ok((&mut 1, None)).is_ok_some());
        }

        #[test]
        fn is_ok_some_not_ok() {
            assert_eq!(false, InsRes::<usize>::Err(KeyErr::ZeroLen).is_ok_some());
        }

        #[test]
        fn uproot_ok_ok() {
            let t = 3usize;
            let proof = (&mut 1, Some(t));
            let test = (&mut 1, Some(t));
            assert_eq!(proof, InsRes::Ok(test).uproot_ok());
        }

        #[test]
        #[should_panic(expected = "Not InsRes::Ok(_) variant.")]
        fn uproot_ok_not_ok() {
            _ = InsRes::<usize>::Err(KeyErr::ZeroLen).uproot_ok();
        }

        #[test]
        fn uproot_ok_some_some() {
            let t = 3usize;
            assert_eq!(t, InsRes::Ok((&mut 1, Some(t))).uproot_ok_some());
        }

        #[test]
        #[should_panic(expected = "Not InsRes::Ok(Some(T)) variant.")]
        fn uproot_ok_some_none() {
            _ = InsRes::<usize>::Ok((&mut 1, None)).uproot_ok_some()
        }

        #[test]
        #[should_panic(expected = "Not InsRes::Ok(Some(T)) variant.")]
        fn uproot_ok_some_not_ok() {
            _ = InsRes::<usize>::Err(KeyErr::ZeroLen).uproot_ok_some()
        }

        #[test]
        fn uproot_ok_unchecked() {
            let t = 3usize;
            let proof = (&mut 1, Some(t));
            let test = (&mut 1, Some(t));
            assert_eq!(proof, InsRes::Ok(test).uproot_ok_unchecked());
        }

        #[test]
        fn uproot_ok_some_unchecked() {
            let t = 3usize;
            let uproot = unsafe { InsRes::Ok((&mut 1, Some(t))).uproot_ok_some_unchecked() };
            assert_eq!(t, uproot);
        }
    }

    mod acq_res {

        use super::super::{AcqRes, KeyErr};

        #[test]
        fn is_ok() {
            let t = 3usize;

            assert_eq!(true, AcqRes::Ok(&t).is_ok());
            assert_eq!(false, AcqRes::<usize>::Err(KeyErr::ZeroLen).is_ok());
        }

        #[test]
        fn uproot() {
            let t = &3usize;
            assert_eq!(t, AcqRes::Ok(t).uproot());
        }

        #[test]
        #[should_panic(expected = "Not AcqRes::Ok(_) variant.")]
        fn uproot_panic() {
            _ = AcqRes::<usize>::Err(KeyErr::ZeroLen).uproot()
        }

        #[test]
        fn uproot_unchecked() {
            let proof = &3usize;
            let res = AcqRes::Ok(proof);
            let test = unsafe { res.uproot_unchecked() };
            assert_eq!(proof, test);
        }
    }

    mod acq_mut_res {

        use super::super::{AcqMutRes, KeyErr};

        #[test]
        fn is_ok() {
            assert_eq!(true, AcqMutRes::Ok(&mut 3).is_ok());
            assert_eq!(false, AcqMutRes::<usize>::Err(KeyErr::ZeroLen).is_ok());
        }

        #[test]
        fn uproot() {
            let t = &mut 3;
            assert_eq!(&mut 3, AcqMutRes::Ok(t).uproot());
        }

        #[test]
        #[should_panic(expected = "Not AcqMutRes::Ok(_) variant.")]
        fn uproot_panic() {
            _ = AcqMutRes::<usize>::Err(KeyErr::ZeroLen).uproot()
        }

        #[test]
        fn uproot_unchecked() {
            let mref = &mut 3usize;
            let mut res = AcqMutRes::Ok(mref);
            let test = unsafe { res.uproot_unchecked() };
            assert_eq!(&mut 3, test);
        }
    }

    mod rem_res {
        use super::super::{KeyErr, RemRes};

        #[test]
        fn is_ok() {
            let t = 3usize;

            assert_eq!(true, RemRes::Ok(t).is_ok());
            assert_eq!(false, RemRes::<usize>::Err(KeyErr::ZeroLen).is_ok());
        }

        #[test]
        fn uproot() {
            let t = 3usize;
            assert_eq!(t, RemRes::Ok(t).uproot());
        }

        #[test]
        #[should_panic(expected = "Not RemRes::Ok(T) variant.")]
        fn uproot_panic() {
            _ = RemRes::<usize>::Err(KeyErr::ZeroLen).uproot()
        }

        #[test]
        fn uproot_unchecked() {
            let t = 3usize;
            let res = RemRes::Ok(t);
            let uproot = unsafe { res.uproot_unchecked() };
            assert_eq!(t, uproot);
        }

        mod clone {
            use super::{KeyErr, RemRes};

            #[test]
            fn ok() {
                let val = 11;
                assert_eq!(RemRes::Ok(val), RemRes::Ok(val).clone());
            }

            #[test]
            fn err() {
                let e = KeyErr::ZeroLen;
                let proof = RemRes::<usize>::Err(e.clone());
                assert_eq!(proof, RemRes::Err(e).clone());
            }
        }
    }
}
