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
/// Check with `english_letters::ix` implementation for lodestar.
pub type Ix = fn(char) -> usize;

/// Reversal index conversion function. Symmetrically mirrors `Ix` function.
///
/// Check with `english_letters::re` for lodestar.
pub type Re = fn(usize) -> char;

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

// TC: Ω(n ⋅alphabet size) ⇒ Ω(n), n = nodes count
// SC: Θ(s +n) ⇒ Θ(s), n = nodes count, s = key lengths sum
// to lower estimation add unpredictible count of string clonings
// and buffers (capacity-) reallocations
fn ext<T>(ab: &mut Alphabet<T>, buff: &mut String, re: Re, o: &mut Vec<(String, T)>) {
    for ix in 0..ab.len() {
        buff.push(re(ix));

        let letter = &mut ab[ix];

        if let Some(e) = letter.en.take() {
            let key = buff.clone();
            o.push((key, e));
        }

        if let Some(ab) = letter.ab.as_mut() {
            ext(ab, buff, re, o);
        }

        _ = buff.pop();
    }
}

// TC: Ω(n ⋅alphabet size) ⇒ Ω(n), n = nodes count
// SC: Θ(s +n) ⇒ Θ(s), n = nodes count, s = key lengths sum
// to lower estimation add unpredictible count of string clonings
// and buffers (capacity-) reallocations
fn view<'a, T>(ab: &'a Alphabet<T>, buff: &mut String, re: Re, o: &mut Vec<(String, &'a T)>) {
    for ix in 0..ab.len() {
        buff.push(re(ix));

        let letter = &ab[ix];

        if let Some(r) = letter.en.as_ref() {
            let key = buff.clone();
            o.push((key, r));
        }

        if let Some(ab) = letter.ab.as_ref() {
            view(ab, buff, re, o);
        }

        _ = buff.pop();
    }
}

/// Module for working with English alphabet small letters, a-z.
///
/// Check with `Trie::new_with()` for more.
pub mod english_letters {

    #[allow(non_upper_case_globals)]
    const a: usize = 'a' as usize;

    /// 26, small letters count.
    pub const ALPHABET_LEN: usize = 26;

    /// Index conversion function.
    pub fn ix(c: char) -> usize {
        let code_point = c as usize;
        match code_point {
            c if c > 96 && c < 123 => c - a,
            _ => panic!("Index conversion failed because code point {code_point} is unsupported."),
        }
    }

    /// Index reversal conversion function.
    pub fn re(i: usize) -> char {
        let code_point = match i {
            i if i < 26 => i + a,
            _ => {
                panic!("Char conversion failed because index `{i}` conversion is not supported.")
            }
        };

        code_point as u8 as char
    }
}

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

#[cfg_attr(test, derive(PartialEq, Debug))]
enum TraRes<'a, T> {
    Ok(&'a Letter<T>),
    OkMut(&'a mut Letter<T>),
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

/// track strain discrete values
mod tsdv {
    pub const NON: u8 = 1;
    pub const TRA: u8 = 2;
    pub const REF: u8 = 4;
    pub const MUT: u8 = 8;
}

#[repr(u8)]
#[derive(Clone)]
enum TraStrain {
    NonRef = tsdv::NON | tsdv::REF,
    NonMut = tsdv::NON | tsdv::MUT,
    TraRef = tsdv::TRA | tsdv::REF,
}

impl TraStrain {
    fn has(self, f: u8) -> bool {
        self as u8 & f == f
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
/// - c is count of `char`s iterated over.
/// - time:  Θ(c).
/// - space: Θ(0).
pub struct Trie<T> {
    // tree root
    rt: Alphabet<T>,
    // index fn
    ix: Ix,
    // rev index fn
    re: Option<Re>,
    // alphabet len
    al: usize,
    // backtrace buff
    tr: Vec<*mut Letter<T>>,
}

impl<T> Trie<T> {
    /// Constructs default version of `Trie`, i.e. via
    /// `fn new_with()` with `english_letters::{ix, re, ALPHABET_LEN}`.
    pub fn new() -> Self {
        Self::new_with(
            english_letters::ix,
            Some(english_letters::re),
            english_letters::ALPHABET_LEN,
        )
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
    ///
    /// // if `fn Trie::ext` or `fn Trie::view` will not be used, pass `None` for `re`
    /// fn re(i: usize) -> char {
    ///     match i {
    ///         0 => '&',
    ///         1 => '|',
    ///        _ => panic!("Only `0` or `1`."),
    ///     }
    /// }    
    ///
    /// let ab_len = 2;
    ///
    /// let mut trie = Trie::new_with(ix, Some(re), ab_len);
    /// let aba = "&|&";
    /// let bab = "|&|";
    /// _ = trie.ins(aba.chars(), 1);
    /// _ = trie.ins(bab.chars(), 2);
    ///
    /// assert_eq!(&1, trie.acq(aba.chars()).uproot());
    /// assert_eq!(&2, trie.acq(bab.chars()).uproot());
    pub fn new_with(ix: Ix, re: Option<Re>, ab_len: usize) -> Self {
        Self {
            rt: ab(ab_len),
            ix,
            re,
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

        let en = &mut letter.en;
        let prev = en.replace(entry);
        let curr = en.as_mut().unwrap();
        InsRes::Ok((curr, prev))
    }

    /// Used to acquire reference to entry of `key`.
    pub fn acq(&self, key: impl Iterator<Item = char>) -> AcqRes<T> {
        let this = unsafe { self.as_mut() };

        match this.track(key, TraStrain::NonRef) {
            TraRes::Ok(l) => {
                let en = l.en.as_ref();
                AcqRes::Ok(unsafe { en.unwrap_unchecked() })
            }
            res => AcqRes::Err(res.key_err()),
        }
    }

    /// Used to acquire mutable reference to entry of `key`.
    pub fn acq_mut(&mut self, key: impl Iterator<Item = char>) -> AcqMutRes<T> {
        match self.track(key, TraStrain::NonMut) {
            TraRes::OkMut(l) => {
                let en = l.en.as_mut();
                AcqMutRes::Ok(unsafe { en.unwrap_unchecked() })
            }
            res => AcqMutRes::Err(res.key_err()),
        }
    }

    unsafe fn as_mut(&self) -> &mut Self {
        let ptr: *const Self = self;
        let mut_ptr: *mut Self = core::mem::transmute(ptr);
        mut_ptr.as_mut().unwrap()
    }

    /// Used to remove key-entry from tree.
    ///
    /// - TC: Ω(c) or ϴ(c). / Backtracing buffer capacity dependent complexity. /
    /// - SC: ϴ(c).
    ///
    /// Check with `put_trace_cap` for details on backtracing.
    pub fn rem(&mut self, key: impl Iterator<Item = char>) -> RemRes<T> {
        let res = match self.track(key, TraStrain::TraRef) {
            TraRes::Ok(_) => {
                let en = self.rem_actual(
                    #[cfg(test)]
                    &mut false,
                );
                RemRes::Ok(en)
            }
            res => RemRes::Err(res.key_err()),
        };

        self.tr.clear();
        res
    }

    fn rem_actual(&mut self, #[cfg(test)] en_esc: &mut bool) -> T {
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
                    #[cfg(test)]
                    {
                        *en_esc = true;
                    }

                    break;
                }
            }
        }

        unsafe { en.unwrap_unchecked() }
    }

    // - c is count of `char`s iterated over
    // - TC: Ω(c) when `tracing = true`, ϴ(c) otherwise
    // - SC: ϴ(c) when `tracing = true`, ϴ(0) otherwise
    fn track<'a>(
        &'a mut self,
        mut key: impl Iterator<Item = char>,
        ts: TraStrain,
    ) -> TraRes<'a, T> {
        let c = key.next();

        if c.is_none() {
            return TraRes::ZeroLen;
        }

        let c = unsafe { c.unwrap_unchecked() };

        let ix = &self.ix;
        let tr = &mut self.tr;

        let mut letter = &mut self.rt[ix(c)];

        let tracing = TraStrain::has(ts.clone(), tsdv::TRA);
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
            if TraStrain::has(ts.clone(), tsdv::REF) {
                TraRes::Ok(letter)
            } else {
                #[cfg(test)]
                assert_eq!(true, TraStrain::has(ts, tsdv::MUT));

                TraRes::OkMut(letter)
            }
        } else {
            TraRes::UnknownForNotEntry
        }
    }

    /// Used to extract key-entry duos from tree. Leaves tree empty.
    ///
    /// Extraction is alphabetically ordered.
    ///
    /// - TC: Ω(n) where n is count of nodes in tree.
    /// - SC: Θ(s) where s is key lengths summation.
    pub fn ext(&mut self) -> Vec<(String, T)> {
        if let Some(re) = self.re {
            // capacity is prebuffered to 1000
            let mut buff = String::with_capacity(1000);

            // capacity is prebuffered to 1000
            let mut res = Vec::with_capacity(1000);

            ext(&mut self.rt, &mut buff, re, &mut res);
            res.shrink_to_fit();

            self.clr();

            res
        } else {
            panic!("This method is unsupported when `new_with` `re` parameter is provided with `None`.");
        }
    }

    /// Used to get view onto key-entry duos in tree.
    ///
    /// View is alphabetically ordered.
    ///
    /// - TC: Ω(n) where n is count of nodes in tree.
    /// - SC: Θ(s) where s is key lengths summation.
    pub fn view(&self) -> Vec<(String, &T)> {
        if let Some(re) = self.re {
            // capacity is prebuffered to 1000
            let mut buff = String::with_capacity(1000);

            // capacity is prebuffered to 1000
            let mut res = Vec::with_capacity(1000);

            view(&self.rt, &mut buff, re, &mut res);
            res.shrink_to_fit();

            res
        } else {
            panic!("This method is unsupported when `new_with` `re` parameter is provided with `None`.");
        }
    }

    /// Used to clear tree.
    ///
    /// TC: Θ(n) where n is count of nodes in tree.
    pub fn clr(&mut self) {
        self.rt = ab(self.al);
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

    mod ext {

        use crate::english_letters::re;
        use crate::{ext, AcqRes, KeyErr, Trie};

        #[test]
        fn basic_test() {
            let mut trie = Trie::new();

            let a = || "a".chars();
            let z = || "z".chars();

            _ = trie.ins(a(), 1usize);
            _ = trie.ins(z(), 2usize);

            let mut buff = String::new();
            let mut test = Vec::new();

            ext(&mut trie.rt, &mut buff, re, &mut test);

            let proof = vec![(String::from("a"), 1), (String::from("z"), 2)];
            assert_eq!(proof, test);

            assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(a()));
            assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(z()));
        }

        #[test]
        fn nesting() {
            let mut trie = Trie::new();

            let entries = [
                ("a", 3),
                ("az", 5),
                ("b", 5),
                ("by", 8),
                ("y", 10),
                ("yb", 12),
                ("z", 99),
                ("za", 103),
            ];

            for e in entries {
                _ = trie.ins(e.0.chars(), e.1);
            }

            let mut buff = String::new();
            let mut test = Vec::new();

            ext(&mut trie.rt, &mut buff, re, &mut test);

            let proof = vec![
                (String::from("a"), 3),
                (String::from("az"), 5),
                (String::from("b"), 5),
                (String::from("by"), 8),
                (String::from("y"), 10),
                (String::from("yb"), 12),
                (String::from("z"), 99),
                (String::from("za"), 103),
            ];

            assert_eq!(proof, test);
        }

        #[test]
        fn in_depth_recursion() {
            let mut trie = Trie::new();

            let paths = [
                ("aa", 13),
                ("azbq", 11),
                ("by", 329),
                ("zazazazazabyyb", 55),
                ("ybc", 7),
                ("ybxr", 53),
                ("ybcrqutmop", 33),
                ("ybcrqutmopfvb", 99),
                ("ybcrqutmoprfg", 80),
            ];

            for p in paths {
                _ = trie.ins(p.0.chars(), p.1);
            }

            let mut buff = String::new();
            let mut test = Vec::new();

            ext(&mut trie.rt, &mut buff, re, &mut test);

            let proof = vec![
                (String::from("aa"), 13),
                (String::from("azbq"), 11),
                (String::from("by"), 329),
                (String::from("ybc"), 7),
                (String::from("ybcrqutmop"), 33),
                (String::from("ybcrqutmopfvb"), 99),
                (String::from("ybcrqutmoprfg"), 80),
                (String::from("ybxr"), 53),
                (String::from("zazazazazabyyb"), 55),
            ];

            assert_eq!(proof, test);
        }
    }

    mod view {

        use crate::english_letters::re;
        use crate::{view, Trie};

        #[test]
        fn basic_test() {
            let mut trie = Trie::new();

            let a = || "a".chars();
            let z = || "z".chars();

            let a_entry = 1usize;
            let z_entry = 2;

            _ = trie.ins(a(), a_entry);
            _ = trie.ins(z(), z_entry);

            let mut buff = String::new();
            let mut test = Vec::new();

            view(&trie.rt, &mut buff, re, &mut test);

            let proof = vec![(String::from("a"), &a_entry), (String::from("z"), &z_entry)];
            assert_eq!(proof, test);
        }

        #[test]
        fn nesting() {
            let mut trie = Trie::new();

            let entries = [
                ("a", 3),
                ("az", 5),
                ("b", 5),
                ("by", 8),
                ("y", 10),
                ("yb", 12),
                ("z", 99),
                ("za", 103),
            ];

            for e in entries {
                _ = trie.ins(e.0.chars(), e.1);
            }

            let mut buff = String::new();
            let mut test = Vec::new();

            view(&trie.rt, &mut buff, re, &mut test);

            let proof = vec![
                (String::from("a"), &3),
                (String::from("az"), &5),
                (String::from("b"), &5),
                (String::from("by"), &8),
                (String::from("y"), &10),
                (String::from("yb"), &12),
                (String::from("z"), &99),
                (String::from("za"), &103),
            ];

            assert_eq!(proof, test);
        }

        #[test]
        fn in_depth_recursion() {
            let mut trie = Trie::new();

            let paths = [
                ("aa", 13),
                ("azbq", 11),
                ("by", 329),
                ("zazazazazabyyb", 55),
                ("ybc", 7),
                ("ybxr", 53),
                ("ybcrqutmop", 33),
                ("ybcrqutmopfvb", 99),
                ("ybcrqutmoprfg", 80),
            ];

            for p in paths {
                _ = trie.ins(p.0.chars(), p.1);
            }

            let mut buff = String::new();
            let mut test = Vec::new();

            view(&trie.rt, &mut buff, re, &mut test);

            let proof = vec![
                (String::from("aa"), &13),
                (String::from("azbq"), &11),
                (String::from("by"), &329),
                (String::from("ybc"), &7),
                (String::from("ybcrqutmop"), &33),
                (String::from("ybcrqutmopfvb"), &99),
                (String::from("ybcrqutmoprfg"), &80),
                (String::from("ybxr"), &53),
                (String::from("zazazazazabyyb"), &55),
            ];

            assert_eq!(proof, test);
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

        mod re {
            use crate::english_letters::re;

            #[test]
            fn ixes() {
                assert_eq!('a', re(0));
                assert_eq!('z', re(25));
            }

            #[test]
            #[should_panic(
                expected = "Char conversion failed because index `26` conversion is not supported."
            )]
            fn unsupported_ix() {
                _ = re(26)
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

        use crate::{AcqMutRes, KeyErr};

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

        mod clone {
            use crate::{KeyErr, RemRes};

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

    mod tra_res {
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
            let mut letter = Letter::<usize>::new();
            _ = TraRes::Ok(&mut letter).key_err()
        }
    }

    mod tra_strain {
        use crate::{tsdv, TraStrain};

        #[test]
        fn has_has() {
            for f in [tsdv::NON, tsdv::REF] {
                assert_eq!(true, TraStrain::has(TraStrain::NonRef, f));
            }
        }

        #[test]
        fn has_has_not() {
            for f in [tsdv::NON, tsdv::MUT] {
                assert_eq!(false, TraStrain::has(TraStrain::TraRef, f));
            }
        }
    }

    mod trie {
        use crate::english_letters::{ix, re, ALPHABET_LEN};
        use crate::{ab, Trie};

        #[test]
        fn new() {
            let trie = Trie::<usize>::new();
            assert_eq!(ALPHABET_LEN, trie.al);
            assert_eq!(ix as usize, trie.ix as usize);
            assert_eq!(re as usize, trie.re.unwrap() as usize);
        }

        #[test]
        fn new_with() {
            fn test_ix(_c: char) -> usize {
                1
            }

            fn test_re(_i: usize) -> char {
                '1'
            }

            let ab_len = 9;
            let trie = Trie::<usize>::new_with(test_ix, Some(test_re), ab_len);

            assert_eq!(ab(ab_len), trie.rt);
            assert_eq!(ab_len, trie.al);
            assert_eq!(test_ix as usize, trie.ix as usize);
            assert_eq!(test_re as usize, trie.re.unwrap() as usize);
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
                let mut entry = 18;
                let update = 19;

                let mut trie = Trie::new();
                let ins_res = trie.ins(keyer(), entry.clone());
                assert_eq!(InsRes::Ok((&mut entry, None)), ins_res);

                let entry_mut = ins_res.uproot_ok().0;
                *entry_mut = update;

                let last_ix = key.len() - 1;
                let mut ultra_ab = &trie.rt;
                for (it_ix, c) in keyer().enumerate() {
                    let terminal_it = it_ix == last_ix;

                    let l = &ultra_ab[ix(c)];
                    let infra_ab = l.ab.as_ref();
                    assert_eq!(terminal_it, infra_ab.is_none());

                    if terminal_it {
                        assert_eq!(Some(update), l.en)
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
                let mut entry = 3;

                let mut trie = Trie::new();
                let ins_res = trie.ins("a".chars(), entry.clone());
                assert_eq!(InsRes::Ok((&mut entry, None)), ins_res);
                assert_eq!(Some(entry), trie.rt[ix('a')].en);
            }

            #[test]
            fn double_insert() {
                let key = "impreciseness";
                let keyer = || key.chars();
                let mut entry_1 = 10;
                let mut entry_2 = 20;

                let mut trie = Trie::new();
                let ins_res_e1 = trie.ins(keyer(), entry_1.clone());
                assert_eq!(InsRes::Ok((&mut entry_1, None)), ins_res_e1);

                let ins_res_e2 = trie.ins(keyer(), entry_2.clone());
                assert_eq!(InsRes::Ok((&mut entry_2, Some(entry_1))), ins_res_e2);

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

        mod acq_mut {
            use crate::{AcqMutRes, KeyErr, Trie};

            #[test]
            fn known_unknown() {
                let a = || "a".chars();
                let b = || "b".chars();
                let mut v = 10;

                let mut trie = Trie::new();
                _ = trie.ins(a(), v);

                assert_eq!(AcqMutRes::Ok(&mut v), trie.acq_mut(a()));
                assert_eq!(AcqMutRes::Err(KeyErr::Unknown), trie.acq_mut(b()));
            }

            #[test]
            fn zero_key() {
                let mut trie = Trie::<usize>::new();
                let test = trie.acq_mut("".chars());
                let proof = AcqMutRes::Err(KeyErr::ZeroLen);
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
            use crate::{AcqRes, KeyErr, TraRes, TraStrain, Trie};

            #[test]
            fn basic_test() {
                let key = || "abcxyz".chars();
                let entry = 60;

                let mut trie = Trie::new();
                _ = trie.ins(key(), entry);

                _ = trie.track(key(), TraStrain::TraRef);

                assert_eq!(entry, trie.rem_actual(&mut false));

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

                let mut trie = Trie::new_with(ix, None, 100);
                _ = trie.ins(key_1(), key_1_val);
                _ = trie.ins(key_2(), key_2_val);

                _ = trie.track(key_1(), TraStrain::TraRef);

                assert_eq!(key_1_val, trie.rem_actual(&mut false));

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

                _ = trie.track(inner(), TraStrain::TraRef);

                assert_eq!(inner_entry, trie.rem_actual(&mut false));

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

                _ = trie.track(test(), TraStrain::TraRef);

                let mut en_esc = false;
                assert_eq!(test_entry, trie.rem_actual(&mut en_esc));
                assert_eq!(false, en_esc);

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

                _ = trie.track(test(), TraStrain::TraRef);

                let mut en_esc = false;
                assert_eq!(test_entry, trie.rem_actual(&mut en_esc));
                assert_eq!(false, en_esc);

                assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(test()));
                assert_eq!(AcqRes::Ok(&peer_entry), trie.acq(peer()));
            }

            #[test]
            fn entry_under_entry() {
                let mut trie = Trie::new();

                let above = || "keyworder".chars();
                let above_entry = 50;
                _ = trie.ins(above(), above_entry);

                let under = || "keyworders".chars();
                let under_entry = 60;
                _ = trie.ins(under(), under_entry);

                _ = trie.track(under(), TraStrain::TraRef);

                let mut en_esc = false;
                assert_eq!(under_entry, trie.rem_actual(&mut en_esc));
                assert_eq!(true, en_esc);

                assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(under()));
                assert_eq!(AcqRes::Ok(&above_entry), trie.acq(above()));

                let res = trie.track(above(), TraStrain::NonRef);
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
            use crate::{TraRes, TraStrain, Trie};

            #[test]
            fn zero_key() {
                let mut trie = Trie::<usize>::new();
                let res = trie.track("".chars(), TraStrain::NonRef);
                assert_eq!(TraRes::ZeroLen, res);
            }

            #[test]
            #[cfg(feature = "test-ext")]
            fn singular_key() {
                let key = || "a".chars();

                let mut trie = Trie::<usize>::new();

                _ = trie.ins(key(), 100);
                let res = trie.track(key(), TraStrain::TraRef);

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
                _ = trie.track(key(), TraStrain::TraRef);

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
                let res = trie.track(key(), TraStrain::NonRef);

                match res {
                    TraRes::Ok(l) => assert_eq!(last, l.val),
                    _ => panic!("TraRes::Ok(_) was expected, instead {:?}.", res),
                }
            }

            #[test]
            #[cfg(feature = "test-ext")]
            fn okmut() {
                let key = || "wordbook".chars();
                let last = 'k';

                let mut trie = Trie::<usize>::new();
                _ = trie.ins(key(), 444);
                let res = trie.track(key(), TraStrain::NonMut);

                match res {
                    TraRes::OkMut(l) => assert_eq!(last, l.val),
                    _ => panic!("TraRes::OkMut(_) was expected, instead {:?}.", res),
                }
            }

            #[test]
            fn unknown_not_path() {
                let key = || "wordbook".chars();
                let bad_key = || "wordbooks".chars();

                let mut trie = Trie::new();
                _ = trie.ins(key(), 500);
                let res = trie.track(bad_key(), TraStrain::NonRef);
                assert_eq!(TraRes::UnknownForAbsentPath, res);
            }

            #[test]
            fn unknown_not_entry() {
                let key = || "wordbooks".chars();
                let bad_key = || "wordbook".chars();

                let mut trie = Trie::new();
                _ = trie.ins(key(), 777);
                let res = trie.track(bad_key(), TraStrain::NonRef);
                assert_eq!(TraRes::UnknownForNotEntry, res);
            }
        }

        mod ext {
            use crate::english_letters::ix;
            use crate::{AcqRes, KeyErr, Trie};

            #[test]
            fn basic_test() {
                let test = vec![
                    (String::from("aa"), 13),
                    (String::from("azbq"), 11),
                    (String::from("by"), 329),
                    (String::from("ybc"), 7),
                    (String::from("ybxr"), 53),
                    (String::from("ybxrqutmop"), 33),
                    (String::from("ybxrqutmopfvb"), 99),
                    (String::from("ybxrqutmoprfg"), 80),
                    (String::from("zazazazazabyyb"), 55),
                ];

                let mut trie = Trie::new();
                for t in test.iter() {
                    _ = trie.ins(t.0.chars(), t.1);
                }

                let ext = trie.ext();
                assert_eq!(test, ext);
                assert!(ext.capacity() < 1000);

                for t in test.iter() {
                    assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(t.0.chars()));
                }
            }

            #[test]
            #[should_panic(
                expected = "This method is unsupported when `new_with` `re` parameter is provided with `None`."
            )]
            fn re_not_provided() {
                _ = Trie::<usize>::new_with(ix, None, 0).ext()
            }
        }

        mod view {
            use crate::english_letters::ix;
            use crate::{AcqRes, Trie};

            #[test]
            fn basic_test() {
                let test = vec![
                    (String::from("aa"), &13),
                    (String::from("azbq"), &11),
                    (String::from("by"), &329),
                    (String::from("ybc"), &7),
                    (String::from("ybxr"), &53),
                    (String::from("ybxrqutmop"), &33),
                    (String::from("ybxrqutmopfvb"), &99),
                    (String::from("ybxrqutmoprfg"), &80),
                    (String::from("zazazazazabyyb"), &55),
                ];

                let mut trie = Trie::new();
                for t in test.iter() {
                    _ = trie.ins(t.0.chars(), *t.1);
                }

                let view = trie.view();
                assert_eq!(test, view);
                assert!(view.capacity() < 1000);

                for t in test.iter() {
                    assert_eq!(AcqRes::Ok(t.1), trie.acq(t.0.chars()));
                }
            }

            #[test]
            #[should_panic(
                expected = "This method is unsupported when `new_with` `re` parameter is provided with `None`."
            )]
            fn re_not_provided() {
                _ = Trie::<usize>::new_with(ix, None, 0).view()
            }
        }

        use crate::{AcqRes, KeyErr};

        #[test]
        fn clr() {
            let key = || "abc".chars();

            let mut trie = Trie::<usize>::new();
            _ = trie.ins(key(), 99);
            trie.clr();

            assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(key()));
            assert_eq!(ab(ALPHABET_LEN), trie.rt);
        }
    }
}

// cargo test --features test-ext --release
// cargo test --release
