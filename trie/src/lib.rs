//! Extendable classic retrieval tree implementation with fixed size alphabet per node.
//!
//! Maps any `T` using any `impl Iterator<Item = char>` type.

use std::vec::Vec;
/// `Letter` is `Alphabet` element, represents tree node.
#[cfg_attr(test, derive(PartialEq))]
struct Letter<T> {
    #[cfg(test)]
    val: char,
    ab: Option<Alphabet<T>>,
    en: Option<T>,
}

impl<T> Letter<T> {
    const fn new() -> Self {
        Letter {
            #[cfg(test)]
            val: '👌',
            ab: None,
            en: None,
        }
    }

    const fn ab(&self) -> bool {
        self.ab.is_some()
    }

    const fn en(&self) -> bool {
        self.en.is_some()
    }
}

/// Tree node arms. Consists of `Letter`s.
type Alphabet<T> = Box<[Letter<T>]>;
/// Index conversion function. Tighten with alphabet used.
/// Returns corresponding `usize`d index of `char`.
///
/// For details see `english_letters::ix` implementation.
pub type Ix = fn(char) -> usize;

/// Alphabet function, tree arms generation of length specified.
fn ab<T>(len: usize) -> Alphabet<T> {
    let mut ab = Vec::new();
    ab.reserve_exact(len);

    let spare = ab.spare_capacity_mut();
    for ix in 0..len {
        let mut _letter = spare[ix].write(Letter::new());

        #[cfg(test)]
        #[cfg(feature = "test-ext")]
        {
            #[allow(non_upper_case_globals)]
            const a: u8 = 'a' as u8;
            _letter.val = (a + ix as u8) as char;
        }
    }

    unsafe { ab.set_len(len) };

    ab.into_boxed_slice()
}

/// Module for working with English alphabet small letters, a-z.
///
/// For details see `Trie::new_with()`.
pub mod english_letters {

    /// 26, small letters count.
    pub const ALPHABET_LEN: usize = 26;

    /// Index conversion function.
    pub fn ix(c: char) -> usize {
        #[allow(non_upper_case_globals)]
        const a: usize = 'a' as usize;

        let code_point = c as usize;
        match code_point {
            c if c > 96 && c < 123 => c - a,
            _ => panic!("Index conversion failed because code point {code_point} is unsupported."),
        }
    }
}

/// Key error enumeration.
#[derive(Debug, PartialEq, Eq)]
pub enum KeyErr {
    /// Zero key usage.
    ZeroLen,
    /// Unknown key usage.
    Unknown,
}

impl<T> From<InsRes<T>> for KeyErr {
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
pub enum InsRes<T> {
    /// Insertion accomplished. Optionally holds previous entry, based on its existence.
    Ok(Option<T>),
    /// Key error.
    Err(KeyErr),
}

impl<T> InsRes<T> {
    /// Returns `true` if `InsRes::Ok(_)`, if not `false`.
    pub const fn is_ok(&self) -> bool {
        match self {
            InsRes::Ok(_) => true,
            _ => false,
        }
    }

    /// Returns `true` if `InsRes::Ok(Some(T))`, if not `false`.
    pub const fn is_ok_some(&self) -> bool {
        if let InsRes::Ok(opt) = self {
            if let Some(_) = opt {
                return true;
            }
        }

        false
    }

    /// Returns `T` of `InsRes::Ok(Some(T))` or _panics_ if:
    /// - not that variant
    /// - `Option<T>` is `None`
    pub fn uproot_ok_some(self) -> T {
        if let InsRes::Ok(opt) = self {
            if let Some(t) = opt {
                return t;
            }
        }

        panic!("Not InsRes::Ok(Some(T)) variant.")
    }

    /// Returns `T` of `InsRes::Ok(Some(T))` and does not _panic_ (UB) if:
    /// - not that variant
    /// - `Option<T>` is `None`
    ///
    /// Check with `std::hint::unreachable_unchecked` for more information.
    pub unsafe fn uproot_ok_some_unchecked(self) -> T {
        if let InsRes::Ok(opt) = self {
            if let Some(t) = opt {
                return t;
            }
        }

        // SAFETY: the safety contract must be upheld by the caller.
        unsafe { std::hint::unreachable_unchecked() }
    }
}

/// Acquisition result enumeration.
#[derive(Debug, PartialEq, Eq)]
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
            _ => panic!("Not AcqRes::Ok(&T) variant."),
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

#[cfg_attr(test, derive(PartialEq, Debug))]
enum TraRes<'a, T> {
    Ok(&'a Letter<T>),
    ZeroLen,
    UnknownForNotEntry,
    UnknownForAbsentPath,
}

impl<'a, T> TraRes<'a, T> {
    fn key_err(&self) -> KeyErr {
        match self {
            TraRes::ZeroLen => KeyErr::ZeroLen,
            TraRes::UnknownForNotEntry | TraRes::UnknownForAbsentPath => KeyErr::Unknown,
            _ => panic!("Unsupported arm match."),
        }
    }
}

/// Trie implementation allowing for mapping any `T` to any `impl Iterator<Item = char>` type.
///
/// OOB English small letters, a–z, support only.
///
/// ```
/// use plain_trie::{Trie, AcqRes};
/// use std::panic::catch_unwind;
///
/// let mut trie = Trie::new();
/// let key = || "oomph".chars();
/// let val = 333;
///
/// _ = trie.ins(key(), val);
/// match trie.acq(key()) {
///     AcqRes::Ok(v) => assert_eq!(&val, v),
///     _ => panic!("Expected AcqRes::Ok(_).")
/// }
///
/// let val = 444;
/// _ = trie.ins(key(), val);
/// match trie.acq(key()) {
///     AcqRes::Ok(v) => assert_eq!(&val, v),
///     _ => panic!("Expected AcqRes::Ok(_).")
/// }
///
/// let catch = catch_unwind(move|| _ = trie.ins("A".chars(), 0));
/// assert!(catch.is_err());
/// ```
///
/// When asymptotic computational complexity is not explicitly specified , it is:
/// - s is count of `char`s iterated over
/// - time:  Θ(s)
/// - space: Θ(0)
pub struct Trie<T> {
    // tree root
    rt: Alphabet<T>,
    // index fn
    ix: Ix,
    // alphabet len
    al: usize,
    // backtrace buff
    tr: Vec<*mut Letter<T>>,
}

impl<T> Trie<T> {
    /// Constructs default version of `Trie`, i.e. via
    /// `fn new_with()` with `english_letters::ab` and `english_letters::ix`.
    pub fn new() -> Self {
        Self::new_with(english_letters::ix, english_letters::ALPHABET_LEN)
    }

    /// Allows to use custom alphabet different from default alphabet.
    ///
    /// ```
    /// use plain_trie::Trie;
    ///
    /// fn ix(c: char) -> usize {
    ///    match c {
    ///        '&' => 0,
    ///        '|' => 1,
    ///        _ => panic!("Only `|` or `&`."),
    ///    }
    /// }
    ///
    /// let ab_len = 2;
    ///
    /// let mut trie = Trie::new_with(ix, ab_len);
    /// let aba = "&|&";
    /// let bab = "|&|";
    /// _ = trie.ins(aba.chars(), 1);
    /// _ = trie.ins(bab.chars(), 2);
    ///
    /// assert_eq!(&1, trie.acq(aba.chars()).uproot());
    /// assert_eq!(&2, trie.acq(bab.chars()).uproot());
    pub fn new_with(ix: Ix, ab_len: usize) -> Self {
        Self {
            rt: ab(ab_len),
            ix,
            al: ab_len,
            tr: Vec::new(),
        }
    }

    /// `Trie` uses internal buffer, to avoid excessive allocations and copying, which grows
    /// over time due backtracing in `rem` method which backtraces whole path from entry
    /// node to root node.
    ///
    /// Use this method to shrink or extend it to fit actual program needs. Neither shrinking nor extending
    /// is guaranteed to be exact. See `Vec::with_capacity()` and `Vec::reserve()`. For optimal `rem` performance, set `approx_cap` to, at least, `key.count()`.
    ///
    /// Some high value is sufficient anyway. Since buffer continuous
    /// usage, its capacity will likely expand at some point in time to size sufficient to all keys.
    ///
    /// Return value is actual buffer capacity.
    ///
    /// **Note:** While `String` is UTF8 encoded, its byte length does not have to equal its `char` count
    /// which is either equal or lesser.
    /// ```
    /// let star = "⭐";
    /// assert_eq!(3, star.len());
    /// assert_eq!(1, star.chars().count());
    ///
    /// let yes = "sí";
    /// assert_eq!(3, yes.len());
    /// assert_eq!(2, yes.chars().nth(1).unwrap().len_utf8());
    ///
    /// let abc = "abc";
    /// assert_eq!(3, abc.len());
    /// ```
    pub fn put_trace_cap(&mut self, approx_cap: usize) -> usize {
        let tr = &mut self.tr;
        let cp = tr.capacity();

        if cp < approx_cap {
            tr.reserve(approx_cap);
        } else if cp > approx_cap {
            *tr = Vec::with_capacity(approx_cap);
        }

        tr.capacity()
    }

    /// Return value is internal backtracing buffer capacity.
    ///
    /// Check with `fn put_trace_cap` for details.
    pub fn acq_trace_cap(&self) -> usize {
        self.tr.capacity()
    }

    /// Return value is `InsRes::Ok(Option<T>)` when operation accomplished. It holds previous
    /// entry, if there was some.
    ///
    /// Only invalid key recognized is zero-length key.
    ///
    /// - SC: Θ(q) where q is number of unique nodes, i.e. `char`s in respective branches.
    pub fn ins(&mut self, mut key: impl Iterator<Item = char>, entry: T) -> InsRes<T> {
        let c = key.next();

        if c.is_none() {
            return InsRes::Err(KeyErr::ZeroLen);
        }

        let c = unsafe { c.unwrap_unchecked() };

        let ix = self.ix;
        let al = self.al;

        let mut letter = &mut self.rt[ix(c)];

        while let Some(c) = key.next() {
            let alphabet = letter.ab.get_or_insert_with(|| ab(al));
            letter = &mut alphabet[ix(c)];
        }

        let prev = letter.en.replace(entry);
        InsRes::Ok(prev)
    }

    /// Used to acquire entry of `key`.
    pub fn acq(&self, key: impl Iterator<Item = char>) -> AcqRes<T> {
        let this = unsafe { self.as_mut() };

        match this.track(key, false) {
            TraRes::Ok(l) => {
                let en = l.en.as_ref();
                AcqRes::Ok(unsafe { en.unwrap_unchecked() })
            }
            res => AcqRes::Err(res.key_err()),
        }
    }

    unsafe fn as_mut(&self) -> &mut Self {
        let ptr: *const Self = self;
        let mut_ptr: *mut Self = core::mem::transmute(ptr);
        mut_ptr.as_mut().unwrap()
    }

    /// Used to remove key-entry from tree.
    ///
    /// - TC: Ω(s) or ϴ(s) / backtracing buffer capacity dependent complexity /
    /// - SC: ϴ(s)
    ///
    /// Check with `put_trace_cap` for details on backtracing.
    pub fn rem(&mut self, key: impl Iterator<Item = char>) -> RemRes<T> {
        let res = match self.track(key, true) {
            TraRes::Ok(_) => {
                let en = Self::rem_actual(self);
                RemRes::Ok(en)
            }
            res => RemRes::Err(res.key_err()),
        };

        self.tr.clear();
        res
    }

    fn rem_actual(&mut self) -> T {
        let mut trace = self.tr.iter_mut().map(|x| unsafe { x.as_mut() }.unwrap());
        let entry = trace.next_back().unwrap();

        let en = entry.en.take();

        if !entry.ab() {
            while let Some(l) = trace.next_back() {
                let alphabet = l.ab.as_ref().unwrap();
                let mut remove_alphab = true;

                for ix in 0..self.al {
                    let letter = &alphabet[ix];

                    if letter.ab() || letter.en() {
                        remove_alphab = false;
                        break;
                    }
                }

                if remove_alphab {
                    l.ab = None;
                } else {
                    break;
                }

                if l.en() {
                    break;
                }
            }
        }

        unsafe { en.unwrap_unchecked() }
    }

    // - s is count of `char`s iterated over.
    // - TC: Ω(s) when `tracing = true`, ϴ(s) otherwise
    // - SC: ϴ(s) when `tracing = true`, ϴ(0) otherwise
    fn track<'a>(
        &'a mut self,
        mut key: impl Iterator<Item = char>,
        tracing: bool,
    ) -> TraRes<'a, T> {
        let c = key.next();

        if c.is_none() {
            return TraRes::ZeroLen;
        }

        let c = unsafe { c.unwrap_unchecked() };

        let ix = &self.ix;
        let tr = &mut self.tr;

        let mut letter = &mut self.rt[ix(c)];

        loop {
            if tracing {
                tr.push(letter)
            }

            if let Some(c) = key.next() {
                if let Some(ab) = letter.ab.as_mut() {
                    letter = &mut ab[ix(c)];
                } else {
                    return TraRes::UnknownForAbsentPath;
                }
            } else {
                break;
            }
        }

        if letter.en() {
            TraRes::Ok(letter)
        } else {
            TraRes::UnknownForNotEntry
        }
    }
}

#[cfg(test)]
mod tests_of_units {

    use crate::Letter;
    use std::fmt::{Debug, Formatter};

    impl<T> Debug for Letter<T> {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            let ab = some_none(self.ab.as_ref());
            let en = some_none(self.en.as_ref());

            return f.write_fmt(format_args!(
                "Letter {{\n  val: {}\n  ab: {}\n  en: {:?}\n}}",
                self.val, ab, en
            ));

            fn some_none<T>(val: Option<&T>) -> &'static str {
                if val.is_some() {
                    "Some"
                } else {
                    "None"
                }
            }
        }
    }

    mod letter {

        use crate::{ab as ab_fn, Letter};

        #[test]
        fn new() {
            let letter = Letter::<usize>::new();

            assert_eq!('👌', letter.val);
            assert!(letter.ab.is_none());
            assert!(letter.en.is_none());
        }

        #[test]
        fn ab() {
            let mut letter = Letter::<usize>::new();
            assert_eq!(false, letter.ab());

            letter.ab = Some(ab_fn(0));
            assert_eq!(true, letter.ab());
        }

        #[test]
        fn en() {
            let mut letter = Letter::<usize>::new();
            assert_eq!(false, letter.en());

            letter.en = Some(0);
            assert_eq!(true, letter.en());
        }
    }

    mod ab {

        use crate::ab as ab_fn;
        use crate::english_letters::ALPHABET_LEN;

        #[test]
        fn ab() {
            let ab = ab_fn::<usize>(ALPHABET_LEN);
            assert_eq!(ALPHABET_LEN, ab.len());

            #[cfg(feature = "test-ext")]
            {
                for (ix, c) in ('a'..='z').enumerate() {
                    let letter = &ab[ix];

                    assert_eq!(c, letter.val);
                    assert!(letter.ab.is_none());
                    assert!(letter.en.is_none());
                }
            }
        }

        #[test]
        fn zero_len() {
            let ab = ab_fn::<usize>(0);
            assert_eq!(0, ab.len());
        }
    }

    mod english_letters {
        use crate::english_letters::ALPHABET_LEN;

        #[test]
        fn consts() {
            assert_eq!(26, ALPHABET_LEN);
        }

        mod ix {
            use crate::english_letters::ix;
            use std::panic::catch_unwind;

            #[test]
            fn ixes() {
                assert_eq!(0, ix('a'));
                assert_eq!(25, ix('z'));
            }

            #[test]
            fn unsupported_char() {
                let ucs = unsupported_chars();

                for (c, cp) in ucs.map(|x| (x as char, x)) {
                    let result = catch_unwind(|| ix(c));
                    assert!(result.is_err());

                    let err = unsafe { result.unwrap_err_unchecked() };
                    let downcast = err.downcast_ref::<String>().unwrap();
                    let proof =
                        format!("Index conversion failed because code point {cp} is unsupported.");
                    assert_eq!(&proof, downcast);
                }
            }

            fn unsupported_chars() -> [u8; 2] {
                #[rustfmt::skip] let ucs =
                [                    
                    'a' as u8 -1, 'z' as u8 +1, // 97–122
                ];

                ucs
            }
        }
    }

    mod key_err {
        use crate::{AcqRes, InsRes, KeyErr, RemRes};

        #[test]
        fn from_ins_res() {
            let from = From::from(InsRes::<usize>::Err(KeyErr::Unknown));
            assert_eq!(KeyErr::Unknown, from);
        }

        #[test]
        #[should_panic(expected = "Not InsRes::Err(_) variant.")]
        fn from_ins_res_panic() {
            let _: KeyErr = From::from(InsRes::<usize>::Ok(None));
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
        use crate::{InsRes, KeyErr};

        #[test]
        fn is_ok() {
            assert_eq!(true, InsRes::<usize>::Ok(None).is_ok());
            assert_eq!(false, InsRes::<usize>::Err(KeyErr::ZeroLen).is_ok());
        }

        #[test]
        fn is_ok_some_some() {
            assert_eq!(true, InsRes::Ok(Some(3)).is_ok_some());
        }

        #[test]
        fn is_ok_some_none() {
            assert_eq!(false, InsRes::<usize>::Ok(None).is_ok_some());
        }

        #[test]
        fn is_ok_some_not_ok() {
            assert_eq!(false, InsRes::<usize>::Err(KeyErr::ZeroLen).is_ok_some());
        }

        #[test]
        fn uproot_ok_some_some() {
            let t = 3usize;
            assert_eq!(t, InsRes::Ok(Some(t)).uproot_ok_some());
        }

        #[test]
        #[should_panic(expected = "Not InsRes::Ok(Some(T)) variant.")]
        fn uproot_ok_some_none() {
            _ = InsRes::<usize>::Ok(None).uproot_ok_some()
        }

        #[test]
        #[should_panic(expected = "Not InsRes::Ok(Some(T)) variant.")]
        fn uproot_ok_some_not_ok() {
            _ = InsRes::<usize>::Err(KeyErr::ZeroLen).uproot_ok_some()
        }

        #[test]
        fn uproot_ok_some_unchecked() {
            let t = 3usize;
            let uproot = unsafe { InsRes::Ok(Some(t)).uproot_ok_some_unchecked() };
            assert_eq!(t, uproot);
        }
    }

    mod acq_res {

        use crate::{AcqRes, KeyErr};

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
        #[should_panic(expected = "Not AcqRes::Ok(&T) variant.")]
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

    mod rem_res {
        use crate::{KeyErr, RemRes};

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
    }

    mod track_res {
        use crate::{KeyErr, Letter, TraRes};

        #[test]
        fn key_err_supported() {
            assert_eq!(KeyErr::ZeroLen, TraRes::<u8>::ZeroLen.key_err());
            assert_eq!(KeyErr::Unknown, TraRes::<u8>::UnknownForNotEntry.key_err());
            assert_eq!(
                KeyErr::Unknown,
                TraRes::<u8>::UnknownForAbsentPath.key_err()
            );
        }

        #[test]
        #[should_panic(expected = "Unsupported arm match.")]
        fn key_err_unsupported() {
            let letter = Letter::<usize>::new();
            _ = TraRes::Ok(&letter).key_err()
        }
    }

    mod trie {
        use crate::english_letters::{ix, ALPHABET_LEN};
        use crate::{ab, Trie};

        #[test]
        fn new() {
            let trie = Trie::<usize>::new();
            assert_eq!(ALPHABET_LEN, trie.al);
            assert_eq!(ix as usize, trie.ix as usize);
        }

        #[test]
        fn new_with() {
            fn test_ix(_c: char) -> usize {
                1
            }

            let ab_len = 9;
            let trie = Trie::<usize>::new_with(test_ix, ab_len);

            assert_eq!(ab(ab_len), trie.rt);
            assert_eq!(ab_len, trie.al);
            assert_eq!(test_ix as usize, trie.ix as usize);
            assert_eq!(0, trie.tr.capacity());
        }

        mod put_trace_cap {
            use crate::Trie;

            #[test]
            fn extend() {
                let new_cap = 10;

                let mut trie = Trie::<usize>::new();
                assert!(trie.tr.capacity() < new_cap);

                let size = trie.put_trace_cap(new_cap);
                assert!(size >= new_cap);
                assert!(trie.tr.capacity() >= new_cap);
            }

            #[test]
            fn shrink() {
                let new_cap = 10;
                let old_cap = 50;

                let mut trie = Trie::<usize>::new();
                trie.tr = Vec::with_capacity(old_cap);

                let size = trie.put_trace_cap(new_cap);
                assert!(size >= new_cap && size < old_cap);
                let cap = trie.tr.capacity();
                assert!(cap >= new_cap && cap < old_cap);
            }

            #[test]
            fn same() {
                let cap = 10;
                let mut trie = Trie::<usize>::new();
                let tr = &mut trie.tr;

                assert!(tr.capacity() < cap);
                tr.reserve_exact(cap);
                let cap = tr.capacity();

                let size = trie.put_trace_cap(cap);
                assert_eq!(cap, size);
                assert_eq!(cap, trie.tr.capacity());
            }
        }

        #[test]
        fn acq_trace_cap() {
            let cap = 10;
            let mut trie = Trie::<usize>::new();
            let tr = &mut trie.tr;

            assert!(tr.capacity() < cap);
            tr.reserve_exact(cap);
            let cap = tr.capacity();

            assert_eq!(cap, trie.acq_trace_cap());
        }

        mod ins {
            use crate::english_letters::ix;
            use crate::{InsRes, KeyErr, Trie};

            #[test]
            fn basic_test() {
                let key = "impreciseness";
                let keyer = || key.chars();
                let entry = 18;

                let mut trie = Trie::new();
                assert_eq!(InsRes::Ok(None), trie.ins(keyer(), entry));

                let last_ix = key.len() - 1;
                let mut ultra_ab = &trie.rt;
                for (it_ix, c) in keyer().enumerate() {
                    let terminal_it = it_ix == last_ix;

                    let l = &ultra_ab[ix(c)];
                    let infra_ab = l.ab.as_ref();
                    assert_eq!(terminal_it, infra_ab.is_none());

                    if terminal_it {
                        assert_eq!(Some(entry), l.en)
                    } else {
                        ultra_ab = unsafe { infra_ab.unwrap_unchecked() };
                    }
                }
            }

            #[test]
            fn zero_key() {
                let mut trie = Trie::new();
                let test = trie.ins("".chars(), 3);
                let proof = InsRes::Err(KeyErr::ZeroLen);
                assert_eq!(proof, test);
            }

            #[test]
            fn singular_key() {
                let entry = 3;

                let mut trie = Trie::new();
                assert_eq!(InsRes::Ok(None), trie.ins("a".chars(), entry));
                assert_eq!(Some(entry), trie.rt[ix('a')].en);
            }

            #[test]
            fn double_insert() {
                let key = "impreciseness";
                let keyer = || key.chars();
                let entry_1 = 10;
                let entry_2 = 20;

                let mut trie = Trie::new();
                assert_eq!(InsRes::Ok(None), trie.ins(keyer(), entry_1));
                assert_eq!(InsRes::Ok(Some(entry_1)), trie.ins(keyer(), entry_2));

                let last_ix = key.len() - 1;
                let mut ultra_ab = &trie.rt;
                for (it_ix, c) in keyer().enumerate() {
                    let terminal_it = it_ix == last_ix;

                    let l = &ultra_ab[ix(c)];
                    let infra_ab = l.ab.as_ref();
                    assert_eq!(terminal_it, infra_ab.is_none());

                    if terminal_it {
                        assert_eq!(Some(entry_2), l.en)
                    } else {
                        ultra_ab = unsafe { infra_ab.unwrap_unchecked() };
                    }
                }
            }
        }

        mod acq {
            use crate::{AcqRes, KeyErr, Trie};

            #[test]
            fn known_unknown() {
                let a = || "a".chars();
                let b = || "b".chars();
                let v = 10;

                let mut trie = Trie::new();
                _ = trie.ins(a(), v);

                assert_eq!(AcqRes::Ok(&v), trie.acq(a()));
                assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(b()));
            }

            #[test]
            fn zero_key() {
                let trie = Trie::<usize>::new();
                let test = trie.acq("".chars());
                let proof = AcqRes::Err(KeyErr::ZeroLen);
                assert_eq!(proof, test);
            }
        }

        #[test]
        fn as_mut() {
            let trie = Trie::<usize>::new();
            let trie_ptr = &trie as *const Trie<usize>;
            let trie_mut = unsafe { trie.as_mut() };
            assert_eq!(trie_ptr as usize, trie_mut as *mut Trie::<usize> as usize);
        }

        mod rem {
            use crate::{AcqRes, KeyErr, RemRes, Trie};

            #[test]
            fn known_unknown() {
                let known = || "plainoperator".chars();
                let unknown = || "secretagent".chars();

                let mut trie = Trie::new();

                let known_entry = 13;
                _ = trie.ins(known(), known_entry);

                assert_eq!(RemRes::Ok(known_entry), trie.rem(known()));
                assert_eq!(0, trie.tr.len());
                assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(known()));

                assert_eq!(RemRes::Err(KeyErr::Unknown), trie.rem(unknown()));
                assert_eq!(0, trie.tr.len());
            }

            #[test]
            fn zero_key() {
                let mut trie = Trie::<usize>::new();
                let test = trie.rem("".chars());
                let proof = RemRes::Err(KeyErr::ZeroLen);
                assert_eq!(proof, test);
            }
        }

        mod rem_actual {
            use crate::english_letters::ix;
            use crate::{AcqRes, KeyErr, TraRes, Trie};

            #[test]
            fn basic_test() {
                let key = || "abcxyz".chars();
                let entry = 60;

                let mut trie = Trie::new();
                _ = trie.ins(key(), entry);

                _ = trie.track(key(), true);

                assert_eq!(entry, Trie::rem_actual(&mut trie));

                let a = &trie.rt[ix('a')];
                assert_eq!(false, a.ab());
            }

            #[test]
            fn ab_len_test() {
                let ix = |c| match c {
                    'a' => 0,
                    'z' => 99,
                    _ => panic!(),
                };

                let key_1 = || "aaa".chars();
                let key_2 = || "aaz".chars();

                let key_1_val = 50;
                let key_2_val = 60;

                let mut trie = Trie::new_with(ix, 100);
                _ = trie.ins(key_1(), key_1_val);
                _ = trie.ins(key_2(), key_2_val);

                _ = trie.track(key_1(), true);

                assert_eq!(key_1_val, Trie::rem_actual(&mut trie));
                assert!(trie.acq(key_2()).is_ok());
            }

            #[test]
            fn inner_entry() {
                let mut trie = Trie::new();

                let outer = || "keyword".chars();
                let outer_entry = 15;
                _ = trie.ins(outer(), outer_entry);

                let inner_entry = 25;
                let inner = || "key".chars();
                _ = trie.ins(inner(), inner_entry);

                _ = trie.track(inner(), true);

                assert_eq!(inner_entry, Trie::rem_actual(&mut trie));
                assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(inner()));
                assert_eq!(AcqRes::Ok(&outer_entry), trie.acq(outer()));
            }

            #[test]
            fn entry_with_peer_entry() {
                let mut trie = Trie::new();

                let peer = || "keyworder".chars();
                let peer_entry = 15;
                _ = trie.ins(peer(), peer_entry);

                let test = || "keywordee".chars();
                let test_entry = 25;
                _ = trie.ins(test(), test_entry);

                _ = trie.track(test(), true);

                assert_eq!(test_entry, Trie::rem_actual(&mut trie));
                assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(test()));
                assert_eq!(AcqRes::Ok(&peer_entry), trie.acq(peer()));
            }

            #[test]
            fn entry_with_peer_with_alphabet() {
                let mut trie = Trie::new();

                let peer = || "keyworders".chars();
                let peer_entry = 11;
                _ = trie.ins(peer(), peer_entry);

                let test = || "keywordee".chars();
                let test_entry = 22;
                _ = trie.ins(test(), test_entry);

                _ = trie.track(test(), true);

                assert_eq!(test_entry, Trie::rem_actual(&mut trie));
                assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(test()));
                assert_eq!(AcqRes::Ok(&peer_entry), trie.acq(peer()));
            }

            // indemonstrable, shortcut would be "executed" anyway in next iteration
            #[test]
            fn entry_under_entry() {
                let mut trie = Trie::new();

                let above = || "keyworder".chars();
                let above_entry = 50;
                _ = trie.ins(above(), above_entry);

                let under = || "keyworders".chars();
                let under_entry = 60;
                _ = trie.ins(under(), under_entry);

                _ = trie.track(under(), true);

                assert_eq!(under_entry, Trie::rem_actual(&mut trie));
                assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(under()));
                assert_eq!(AcqRes::Ok(&above_entry), trie.acq(above()));

                let res = trie.track(above(), false);
                if let TraRes::Ok(l) = res {
                    #[cfg(feature = "test-ext")]
                    assert_eq!('r', l.val);
                    assert_eq!(false, l.ab());
                } else {
                    panic!("TraRes::Ok(_) was expected, instead {:?}.", res);
                }
            }
        }

        mod track {
            use crate::{TraRes, Trie};

            #[test]
            fn zero_key() {
                let mut trie = Trie::<usize>::new();
                let res = trie.track("".chars(), false);
                assert_eq!(TraRes::ZeroLen, res);
            }

            #[test]
            #[cfg(feature = "test-ext")]
            fn singular_key() {
                let key = || "a".chars();

                let mut trie = Trie::<usize>::new();

                _ = trie.ins(key(), 100);
                let res = trie.track(key(), true);

                if let TraRes::Ok(l) = res {
                    let l_val = l.val;
                    let tr = &trie.tr;

                    assert_eq!('a', l_val);
                    assert_eq!(1, tr.len());

                    let l = unsafe { tr[0].as_ref() }.unwrap();
                    assert_eq!('a', l.val)
                } else {
                    panic!("TraRes::Ok(_) was expected, instead {:?}.", res);
                }
            }

            #[test]
            #[cfg(feature = "test-ext")]
            fn tracing() {
                let key = || "dictionarylexicon".chars();

                let mut trie = Trie::<usize>::new();
                _ = trie.ins(key(), 999);
                _ = trie.track(key(), true);

                let proof = key().collect::<Vec<char>>();
                let tr = &trie.tr;

                assert_eq!(proof.len(), tr.len());

                for (x, &c) in proof.iter().enumerate() {
                    let l = tr[x];
                    let l = unsafe { l.as_ref() }.unwrap();
                    assert_eq!(c, l.val);
                }
            }

            #[test]
            #[cfg(feature = "test-ext")]
            fn ok() {
                let key = || "wordbook".chars();
                let last = 'k';

                let mut trie = Trie::<usize>::new();
                _ = trie.ins(key(), 444);
                let res = trie.track(key(), false);

                match res {
                    TraRes::Ok(l) => assert_eq!(last, l.val),
                    _ => panic!("TraRes::Ok(_) was expected, instead {:?}.", res),
                }
            }

            #[test]
            fn unknown_not_path() {
                let key = || "wordbook".chars();
                let bad_key = || "wordbooks".chars();

                let mut trie = Trie::new();
                _ = trie.ins(key(), 500);
                let res = trie.track(bad_key(), false);
                assert_eq!(TraRes::UnknownForAbsentPath, res);
            }

            #[test]
            fn unknown_not_entry() {
                let key = || "wordbooks".chars();
                let bad_key = || "wordbook".chars();

                let mut trie = Trie::new();
                _ = trie.ins(key(), 777);
                let res = trie.track(bad_key(), false);
                assert_eq!(TraRes::UnknownForNotEntry, res);
            }
        }
    }
}

// cargo test --features test-ext --release
