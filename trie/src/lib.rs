//! Extendable classic retrieval tree implementation with fixed size alphabet per node.
//!
//! Maps any `T` using any `impl Iterator<Item = char>` type.

mod res;
pub use res::{InsRes, InsResAide, KeyErr};

mod uc;
use uc::UC;

mod tra;
use tra::{tsdv, TraStrain};

use std::vec::Vec;
/// [`Letter`] is [`Alphabet`] element, represents tree node.
#[cfg_attr(test, derive(PartialEq))]
pub struct Letter<T> {
    #[cfg(test)]
    val: char,
    /// Arms to sub-level tree nodes, if some exist.
    pub ab: Option<Alphabet<T>>,
    /// `T` type entry, if node is entry node.
    pub en: Option<T>,
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

    const fn to_mut_ptr(&self) -> *mut Self {
        (self as *const Self).cast_mut()
    }
}

/// Tree node arms. Consists of [`Letter`]s.
pub type Alphabet<T> = Box<[Letter<T>]>;
/// Index conversion function. Tighten with alphabet used.
/// Returns corresponding [`usize`]d index of [`char`].
///
/// Check with [`english_letters::ix`] implementation for lodestar.
pub type Ix = fn(char) -> usize;

/// Reversal index conversion function. Symmetrically mirrors [`Ix`] function.
///
/// Check with [`english_letters::re`] for lodestar.
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
// SC: ϴ(s) for small sized Ts or ϴ(s +n ⋅`size_of<T>`) ⇒ ϴ(s +n), n = nodes count, s = key lengths sum
// to lower estimation add most notably unpredictable count of string clonings
// and buffers capacity-reallocations
fn ext<T>(ab: &mut Alphabet<T>, buff: &mut String, re: Re, o: &mut Vec<(String, T)>) {
    let len = ab.len();
    let mut ix = 0;
    while ix < len {
        buff.push(re(ix));

        let letter = &mut ab[ix];
        ix += 1;

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
// SC: ϴ(n ⋅size_of<T>) ⇒ ϴ(n), n = nodes count
// to lower estimation adds most notably unpredictable
// count of buffer capacity-reallocations
fn vals<T>(ab: &Alphabet<T>, o: &mut Vec<T>)
where
    T: Clone,
{
    let len = ab.len();
    let mut ix = 0;
    while ix < len {
        let letter = &ab[ix];
        ix += 1;

        if let Some(e) = letter.en.as_ref() {
            let c = e.clone();
            o.push(c);
        }

        if let Some(ab) = letter.ab.as_ref() {
            vals(ab, o);
        }
    }
}

// TC: Ω(n ⋅alphabet size) ⇒ Ω(n), n = nodes count
// SC: ϴ(s), s = key lengths sum
// to lower estimation add most notably unpredictable count of string clonings
// and buffer capacity-reallocations
fn keys<T>(ab: &Alphabet<T>, buff: &mut String, re: Re, o: &mut Vec<String>) {
    let len = ab.len();
    let mut ix = 0;
    while ix < len {
        buff.push(re(ix));

        let letter = &ab[ix];
        ix += 1;

        if letter.en.is_some() {
            let key = buff.clone();
            o.push(key);
        }

        if let Some(ab) = letter.ab.as_ref() {
            keys(ab, buff, re, o);
        }

        _ = buff.pop();
    }
}

// TC: Ω(n ⋅alphabet size) ⇒ Ω(n), n = nodes count
// SC: ϴ(s), s = key lengths sum
// to lower estimation add most notably unpredictable count of string clonings
// and buffers capacity-reallocations
fn view<'a, T>(ab: &'a Alphabet<T>, buff: &mut String, re: Re, o: &mut Vec<(String, &'a T)>) {
    let len = ab.len();
    let mut ix = 0;
    while ix < len {
        buff.push(re(ix));

        let letter = &ab[ix];
        ix += 1;

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
/// Check with [`Trie::new_with()`] for more.
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

#[cfg_attr(test, derive(PartialEq, Debug))]
enum TraRes<'a, T> {
    Ok,
    OkRef(&'a Letter<T>),
    OkMut(&'a mut Letter<T>),
    ZeroLen,
    UnknownForNotEntry,
    UnknownForAbsentPath,
}

impl<'a, T> TraRes<'a, T> {
    const fn key_err(&self) -> KeyErr {
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
/// use plain_trie::Trie;
/// use std::panic::catch_unwind;
///
/// let mut trie = Trie::new();
/// let key = || "oomph".chars();
/// let val = 333;
///
/// _ = trie.ins(key(), val);
/// match trie.acq(key()) {
///     Ok(v) => assert_eq!(&val, v),
///     _ => panic!("Expected Ok(_).")
/// }
///
/// let val = 444;
/// _ = trie.ins(key(), val);
/// match trie.acq(key()) {
///     Ok(v) => assert_eq!(&val, v),
///     _ => panic!("Expected Ok(_).")
/// }
///
/// let catch = catch_unwind(move|| _ = trie.ins("A".chars(), 0));
/// assert!(catch.is_err());
/// ```
///
/// When asymptotic computational complexity (ACC) is not explicitly specified , it is:
/// - time:  ϴ(c).
/// - space: ϴ(0).
///
///  ACC can use these size metrics:
/// - n — nodes count
/// - q — unique nodes count
/// - c — `char`s iterated over count
/// - s — string lengths summation
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
    tr: UC<Vec<*mut Letter<T>>>,
    // entries count
    ct: usize,
}

const RE_MISS: &str =
    "This method is unsupported when `new_with` `re` parameter is provided with `None`.";
impl<T> Trie<T> {
    /// Constructs default version of [`Trie`], i.e. via
    /// [`Trie::new_with()`] with [`english_letters`]`::{ix, re, ALPHABET_LEN}`.
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
    /// assert_eq!(&1, trie.acq(aba.chars()).unwrap());
    /// assert_eq!(&2, trie.acq(bab.chars()).unwrap());
    pub fn new_with(ix: Ix, re: Option<Re>, ab_len: usize) -> Self {
        Self {
            rt: ab(ab_len),
            ix,
            re,
            al: ab_len,
            tr: UC::new(Vec::new()),
            ct: 0,
        }
    }

    /// [`Trie`] uses internal buffer, to avoid excessive allocations and copying, which grows
    /// over time due backtracing in [`Trie::rem`] method which holds backtrace of whole path from entry
    /// node to root node.
    ///
    /// Use this method to shrink or extend it to fit actual program needs. Neither shrinking nor extending
    /// is guaranteed to be exact. See [`Vec::with_capacity()`] and [`Vec::reserve()`]. For optimal [`Trie::rem`] performance, set `approx_cap` to, at least, `key.count()`.
    ///
    /// Some high value is sufficient anyway. Since buffer continuous
    /// usage, its capacity will likely expand at some point in time to size sufficient to all keys.
    ///
    /// Return value is actual buffer capacity.
    ///
    /// **Note:** While [`String`] is UTF8 encoded, its byte length does not have to equal its [`char`] count
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
            tr.get_mut().reserve(approx_cap);
        } else if cp > approx_cap {
            *tr = UC::new(Vec::with_capacity(approx_cap));
        }

        tr.capacity()
    }

    /// Return value is internal backtracing buffer capacity.
    ///
    /// Check with [`Trie::put_trace_cap`] for details.
    pub fn acq_trace_cap(&self) -> usize {
        self.tr.capacity()
    }

    /// Used to insert entry into tree under key specified.
    ///
    /// Only invalid key classified is zero-length key.
    ///
    /// - SC: ϴ(q).
    ///
    /// ```
    /// use plain_trie::{Trie, InsResAide};
    ///
    /// let mut trie = Trie::new();
    /// let mut key = || "abc".chars();
    ///
    /// let test = trie.ins(key(), 3);
    /// assert!(test.is_ok());
    ///
    /// let test = trie.ins(key(), 4);
    /// assert_eq!(3, test.unwrap().uproot_previous());
    /// ```
    pub fn ins(
        &mut self,
        mut key: impl Iterator<Item = char>,
        entry: T,
    ) -> Result<InsRes<'_, T>, KeyErr> {
        let c = key.next();

        if c.is_none() {
            return Err(KeyErr::ZeroLen);
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

        if prev.is_none() {
            self.ct += 1;
        }

        let curr = en.as_mut().unwrap();
        Ok((curr, prev))
    }

    /// Used to acquire reference to entry of `key`.
    pub fn acq(&self, key: impl Iterator<Item = char>) -> Result<&T, KeyErr> {
        match self.track(key, TraStrain::NonRef) {
            TraRes::OkRef(l) => {
                let en = l.en.as_ref();
                Ok(unsafe { en.unwrap_unchecked() })
            }
            res => Err(res.key_err()),
        }
    }

    /// Used to acquire mutable reference to entry of `key`.
    pub fn acq_mut(&mut self, key: impl Iterator<Item = char>) -> Result<&mut T, KeyErr> {
        match self.track(key, TraStrain::NonMut) {
            TraRes::OkMut(l) => {
                let en = l.en.as_mut();
                Ok(unsafe { en.unwrap_unchecked() })
            }
            res => Err(res.key_err()),
        }
    }

    /// Used to remove key-entry from tree.
    ///
    /// - TC: Ω(c) or ϴ(c). / Backtracing buffer capacity dependent complexity. /
    /// - SC: ϴ(c).
    ///
    /// Check with [`Trie::put_trace_cap`] for details on backtracing.
    pub fn rem(&mut self, key: impl Iterator<Item = char>) -> Result<T, KeyErr> {
        let res = match self.track(key, TraStrain::TraEmp) {
            TraRes::Ok => {
                let en = self.rem_actual(
                    #[cfg(test)]
                    &mut false,
                );

                self.ct -= 1;
                Ok(en)
            }
            res => Err(res.key_err()),
        };

        self.tr.get_mut().clear();
        res
    }

    fn rem_actual(&mut self, #[cfg(test)] en_esc: &mut bool) -> T {
        let mut trace = self
            .tr
            .get_ref()
            .iter()
            .map(|x| unsafe { x.as_mut() }.unwrap());
        let entry = unsafe { trace.next_back().unwrap_unchecked() };

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
    fn track<'a>(&'a self, mut key: impl Iterator<Item = char>, ts: TraStrain) -> TraRes<'a, T> {
        let c = key.next();

        if c.is_none() {
            return TraRes::ZeroLen;
        }

        let c = unsafe { c.unwrap_unchecked() };

        let ix = &self.ix;
        let tr = self.tr.get_mut();

        let mut letter = &self.rt[ix(c)];

        let tracing = TraStrain::has(ts.clone(), tsdv::TRA);
        loop {
            if tracing {
                tr.push(letter.to_mut_ptr())
            }

            if let Some(c) = key.next() {
                if let Some(ab) = letter.ab.as_ref() {
                    letter = &ab[ix(c)];
                } else {
                    return TraRes::UnknownForAbsentPath;
                }
            } else {
                break;
            }
        }

        if letter.en() {
            match ts {
                x if TraStrain::has(x.clone(), tsdv::REF) => TraRes::OkRef(letter),
                x if TraStrain::has(x.clone(), tsdv::MUT) => {
                    let l_mut = unsafe { letter.to_mut_ptr().as_mut().unwrap_unchecked() };
                    TraRes::OkMut(l_mut)
                }
                x if TraStrain::has(x.clone(), tsdv::EMP) => TraRes::Ok,
                _ => panic!("Unsupported result scenario."),
            }
        } else {
            TraRes::UnknownForNotEntry
        }
    }

    /// Used to extract key-entry duos from tree. Leaves tree empty.
    ///
    /// Extraction is alphabetically ordered, exactly according to [`Re`] function.
    ///
    /// Return value is [`None`] for empty [`Trie<T>`].
    ///
    /// - TC: Ω(n).
    /// - SC: ϴ(s) for small sized Ts or ϴ(s +n).
    pub fn ext(&mut self) -> Option<Vec<(String, T)>> {
        if let Some(re) = self.re {
            let ct = self.ct;
            if ct == 0 {
                return None;
            }

            // capacity is prebuffered to 1000
            let mut buff = String::with_capacity(1000);

            let mut res = Vec::new();
            res.reserve_exact(ct);

            ext(&mut self.rt, &mut buff, re, &mut res);
            _ = self.clr();

            Some(res)
        } else {
            panic!("{}", RE_MISS);
        }
    }

    /// Used to acquire cloned values from tree.
    ///
    /// Extraction is alphabetically ordered, exactly according to [`Ix`] function.
    ///
    /// Return value is [`None`] for empty [`Trie<T>`].
    ///
    /// - TC: ϴ(n).
    /// - SC: ϴ(n).
    pub fn vals(&self) -> Option<Vec<T>>
    where
        T: Clone,
    {
        let ct = self.ct;
        if ct == 0 {
            return None;
        }

        let mut res = Vec::new();
        res.reserve_exact(ct);

        vals(&self.rt, &mut res);

        Some(res)
    }

    /// Used to acquire keys of entries in tree.
    ///
    /// Extraction is alphabetically ordered, exactly according to [`Re`] function.
    ///
    /// Return value is [`None`] for empty [`Trie<T>`].
    ///
    /// - TC: Ω(n).
    /// - SC: ϴ(s).
    pub fn keys(&self) -> Option<Vec<String>> {
        if let Some(re) = self.re {
            let ct = self.ct;
            if ct == 0 {
                return None;
            }

            // capacity is prebuffered to 1000
            let mut buff = String::with_capacity(1000);

            let mut res = Vec::new();
            res.reserve_exact(ct);

            keys(&self.rt, &mut buff, re, &mut res);

            Some(res)
        } else {
            panic!("{}", RE_MISS);
        }
    }

    /// Used to get view onto key-entry duos in tree.
    ///
    /// View is alphabetically ordered, exactly according to [`Re`] function.
    ///
    /// Return value is [`None`] for empty [`Trie<T>`].
    ///
    /// - TC: Ω(n).
    /// - SC: ϴ(s).
    pub fn view(&self) -> Option<Vec<(String, &T)>> {
        if let Some(re) = self.re {
            let ct = self.ct;
            if ct == 0 {
                return None;
            }

            // capacity is prebuffered to 1000
            let mut buff = String::with_capacity(1000);

            let mut res = Vec::new();
            res.reserve_exact(ct);

            view(&self.rt, &mut buff, re, &mut res);
            Some(res)
        } else {
            panic!("{}", RE_MISS);
        }
    }

    /// Used to clear tree.
    ///
    /// Return value is count of entries before clearing.
    ///
    /// TC: ϴ(n).
    pub fn clr(&mut self) -> usize {
        self.rt = ab(self.al);
        let ct = self.ct;
        self.ct = 0;
        ct
    }

    /// Used to acquire count of entries in tree.
    pub const fn ct(&self) -> usize {
        self.ct
    }

    /// Provides reference access to tree root arms.
    ///
    /// Intended for functional extension of trie.
    pub fn as_ref(&self) -> &Alphabet<T> {
        &self.rt
    }

    /// Provides mutable reference access to tree root arms.
    ///
    /// Intended for functional extension of trie.
    pub fn as_mut(&mut self) -> &mut Alphabet<T> {
        &mut self.rt
    }
}

#[cfg(test)]
mod aide;

#[cfg(test)]
mod tests_of_units {

    use crate::Letter;
    use std::fmt::{Debug, Formatter};

    impl<T> Debug for Letter<T> {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            let ab = some_none(self.ab.as_ref());
            let en = some_none(self.en.as_ref());

            return f.write_fmt(format_args!(
                "Letter {{\n  val: {}\n  ab: {}\n  en: {}\n}}",
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
        use crate::{ext, KeyErr, Trie};

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

            assert_eq!(Err(KeyErr::Unknown), trie.acq(a()));
            assert_eq!(Err(KeyErr::Unknown), trie.acq(z()));
        }

        #[test]
        fn nesting() {
            let mut trie = Trie::new();

            let entries = vec![
                (String::from("a"), 3),
                (String::from("az"), 5),
                (String::from("b"), 5),
                (String::from("by"), 8),
                (String::from("y"), 10),
                (String::from("yb"), 12),
                (String::from("z"), 99),
                (String::from("za"), 103),
            ];

            for e in entries.iter() {
                _ = trie.ins(e.0.chars(), e.1);
            }

            let mut buff = String::new();
            let mut test = Vec::new();

            ext(&mut trie.rt, &mut buff, re, &mut test);

            assert_eq!(entries, test);
        }

        #[test]
        fn in_depth_recursion() {
            let mut trie = Trie::new();

            let paths = vec![
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

            for p in paths.iter() {
                _ = trie.ins(p.0.chars(), p.1);
            }

            let mut buff = String::new();
            let mut test = Vec::new();

            ext(&mut trie.rt, &mut buff, re, &mut test);

            assert_eq!(paths, test);
        }
    }

    mod vals {

        use crate::{vals, Trie};

        #[test]
        fn basic_test() {
            let mut trie = Trie::new();

            let a = || "a".chars();
            let z = || "z".chars();

            _ = trie.ins(a(), 1usize);
            _ = trie.ins(z(), 2usize);

            let mut test = Vec::new();

            vals(&mut trie.rt, &mut test);

            let proof = vec![1, 2];
            assert_eq!(proof, test);

            assert_eq!(true, trie.acq(a()).is_ok());
            assert_eq!(true, trie.acq(z()).is_ok());
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

            for e in entries.iter() {
                _ = trie.ins(e.0.chars(), e.1);
            }

            let mut test = Vec::new();

            vals(&mut trie.rt, &mut test);

            for zip in entries.iter().zip(test.iter()) {
                assert_eq!(zip.0 .1, *zip.1);
            }
        }

        #[test]
        fn in_depth_recursion() {
            let mut trie = Trie::new();

            let paths = [
                ("aa", 13),
                ("azbq", 11),
                ("by", 329),
                ("ybc", 7),
                ("ybcrqutmop", 33),
                ("ybcrqutmopfvb", 99),
                ("ybcrqutmoprfg", 80),
                ("ybxr", 53),
                ("zazazazazabyyb", 55),
            ];

            for p in paths.iter() {
                _ = trie.ins(p.0.chars(), p.1);
            }

            let mut test = Vec::new();

            vals(&mut trie.rt, &mut test);

            for zip in paths.iter().zip(test.iter()) {
                assert_eq!(zip.0 .1, *zip.1);
            }
        }
    }

    mod keys {

        use crate::english_letters::re;
        use crate::{keys, Trie};

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

            keys(&trie.rt, &mut buff, re, &mut test);

            let proof = vec![String::from("a"), String::from("z")];
            assert_eq!(proof, test);
        }

        #[test]
        fn nesting() {
            let mut trie = Trie::new();

            let entries = vec![
                (String::from("a"), 3),
                (String::from("az"), 5),
                (String::from("b"), 5),
                (String::from("by"), 8),
                (String::from("y"), 10),
                (String::from("yb"), 12),
                (String::from("z"), 99),
                (String::from("za"), 103),
            ];

            for e in entries.iter() {
                _ = trie.ins(e.0.chars(), e.1);
            }

            let mut buff = String::new();
            let mut test = Vec::new();

            keys(&trie.rt, &mut buff, re, &mut test);

            for zip in entries.iter().zip(test.iter()) {
                assert_eq!(zip.0 .0, *zip.1);
            }
        }

        #[test]
        fn in_depth_recursion() {
            let mut trie = Trie::new();

            let paths = vec![
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

            for p in paths.iter() {
                _ = trie.ins(p.0.chars(), p.1);
            }

            let mut buff = String::new();
            let mut test = Vec::new();

            keys(&trie.rt, &mut buff, re, &mut test);

            for zip in paths.iter().zip(test.iter()) {
                assert_eq!(zip.0 .0, *zip.1);
            }
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

            let entries = vec![
                (String::from("a"), &3),
                (String::from("az"), &5),
                (String::from("b"), &5),
                (String::from("by"), &8),
                (String::from("y"), &10),
                (String::from("yb"), &12),
                (String::from("z"), &99),
                (String::from("za"), &103),
            ];

            for e in entries.iter() {
                _ = trie.ins(e.0.chars(), *e.1);
            }

            let mut buff = String::new();
            let mut test = Vec::new();

            view(&trie.rt, &mut buff, re, &mut test);

            assert_eq!(entries, test);
        }

        #[test]
        fn in_depth_recursion() {
            let mut trie = Trie::new();

            let paths = vec![
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

            for p in paths.iter() {
                _ = trie.ins(p.0.chars(), *p.1);
            }

            let mut buff = String::new();
            let mut test = Vec::new();

            view(&trie.rt, &mut buff, re, &mut test);

            assert_eq!(paths, test);
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

    mod tra_res {
        use crate::{KeyErr, TraRes};

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
            _ = TraRes::<usize>::Ok.key_err()
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
            assert_eq!(0, trie.ct);
        }

        mod put_trace_cap {
            use crate::{uc::UC, Trie};

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
                trie.tr = UC::new(Vec::with_capacity(old_cap));

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
                tr.get_mut().reserve_exact(cap);
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
            tr.get_mut().reserve_exact(cap);
            let cap = tr.capacity();

            assert_eq!(cap, trie.acq_trace_cap());
        }

        mod ins {
            use crate::english_letters::ix;
            use crate::{KeyErr, Trie};

            #[test]
            fn basic_test() {
                let key = "impreciseness";
                let keyer = || key.chars();
                let mut entry = 18;
                let update = 19;

                let mut trie = Trie::new();
                let ins_res = trie.ins(keyer(), entry);
                assert_eq!(Ok((&mut entry, None)), ins_res);

                let entry_mut = ins_res.unwrap().0;
                *entry_mut = update;

                let last_ix = key.len() - 1;
                let mut albet = &trie.rt;
                for (it_ix, c) in keyer().enumerate() {
                    let l = &albet[ix(c)];

                    if it_ix == last_ix {
                        assert_eq!(false, l.ab());
                        assert_eq!(Some(update), l.en)
                    } else {
                        assert_eq!(true, l.ab());
                        albet = l.ab.as_ref().unwrap();
                    }
                }

                assert_eq!(1, trie.ct);
            }

            #[test]
            fn zero_key() {
                let mut trie = Trie::new();
                let test = trie.ins("".chars(), 3);
                let proof = Err(KeyErr::ZeroLen);
                assert_eq!(proof, test);
                assert_eq!(0, trie.ct);
            }

            #[test]
            fn singular_key() {
                let mut entry = 3;

                let mut trie = Trie::new();
                let ins_res = trie.ins("a".chars(), entry);
                assert_eq!(Ok((&mut entry, None)), ins_res);
                assert_eq!(Some(entry), trie.rt[ix('a')].en);
                assert_eq!(1, trie.ct);
            }

            #[test]
            fn double_insert() {
                let key = "impreciseness";
                let keyer = || key.chars();
                let mut entry_1 = 10;
                let mut entry_2 = 20;

                let mut trie = Trie::new();
                let ins_res_e1 = trie.ins(keyer(), entry_1);
                assert_eq!(Ok((&mut entry_1, None)), ins_res_e1);
                assert_eq!(1, trie.ct);

                let ins_res_e2 = trie.ins(keyer(), entry_2);
                assert_eq!(Ok((&mut entry_2, Some(entry_1))), ins_res_e2);
                assert_eq!(1, trie.ct);

                let last_ix = key.len() - 1;
                let mut albet = &trie.rt;
                for (it_ix, c) in keyer().enumerate() {
                    let l = &albet[ix(c)];

                    if it_ix == last_ix {
                        assert_eq!(false, l.ab());
                        assert_eq!(Some(entry_2), l.en)
                    } else {
                        assert_eq!(true, l.ab());
                        albet = l.ab.as_ref().unwrap();
                    }
                }
            }
        }

        mod acq {
            use crate::{KeyErr, Trie};

            #[test]
            fn known_unknown() {
                let a = || "a".chars();
                let b = || "b".chars();
                let v = 10;

                let mut trie = Trie::new();
                _ = trie.ins(a(), v);

                assert_eq!(Ok(&v), trie.acq(a()));
                assert_eq!(Err(KeyErr::Unknown), trie.acq(b()));
            }

            #[test]
            fn zero_key() {
                let trie = Trie::<usize>::new();
                let test = trie.acq("".chars());
                let proof = Err(KeyErr::ZeroLen);
                assert_eq!(proof, test);
            }
        }

        mod acq_mut {
            use crate::{KeyErr, Trie};

            #[test]
            fn known_unknown() {
                let a = || "a".chars();
                let b = || "b".chars();
                let mut v = 10;

                let mut trie = Trie::new();
                _ = trie.ins(a(), v);

                assert_eq!(Ok(&mut v), trie.acq_mut(a()));
                assert_eq!(Err(KeyErr::Unknown), trie.acq_mut(b()));
            }

            #[test]
            fn zero_key() {
                let mut trie = Trie::<usize>::new();
                let test = trie.acq_mut("".chars());
                let proof = Err(KeyErr::ZeroLen);
                assert_eq!(proof, test);
            }
        }

        mod rem {
            use crate::{KeyErr, Trie};

            #[test]
            fn known_unknown() {
                let known = || "plainoperator".chars();
                let unknown = || "secretagent".chars();

                let mut trie = Trie::new();

                let known_entry = 13;
                _ = trie.ins(known(), known_entry);

                assert_eq!(Err(KeyErr::Unknown), trie.rem(unknown()));
                assert_eq!(0, trie.tr.len());
                assert_eq!(1, trie.ct);

                assert_eq!(Ok(known_entry), trie.rem(known()));
                assert_eq!(0, trie.tr.len());
                assert_eq!(0, trie.ct);
                assert_eq!(Err(KeyErr::Unknown), trie.acq(known()));
            }

            #[test]
            fn zero_key() {
                let mut trie = Trie::<usize>::new();
                let test = trie.rem("".chars());
                let proof = Err(KeyErr::ZeroLen);
                assert_eq!(proof, test);
            }
        }

        mod rem_actual {
            use crate::english_letters::ix;
            use crate::{KeyErr, TraRes, TraStrain, Trie};

            #[test]
            fn basic_test() {
                let key = || "abcxyz".chars();
                let entry = 60;

                let mut trie = Trie::new();
                _ = trie.ins(key(), entry);

                _ = trie.track(key(), TraStrain::TraEmp);

                assert_eq!(entry, trie.rem_actual(&mut false));

                let a = &trie.rt[ix('a')];
                assert_eq!(false, a.ab());
            }

            #[test]
            fn one_letter_a() {
                let key = || "a".chars();
                let entry = 60;

                let mut trie = Trie::new();
                _ = trie.ins(key(), entry);

                _ = trie.track(key(), TraStrain::TraEmp);

                let mut en_esc = false;
                assert_eq!(entry, trie.rem_actual(&mut en_esc));
                assert_eq!(Err(KeyErr::Unknown), trie.acq(key()));
                assert_eq!(false, en_esc);
            }

            #[test]
            fn one_letter_b() {
                let key1 = || "a".chars();
                let key2 = || "b".chars();
                let entry1 = 50;
                let entry2 = 60;

                let mut trie = Trie::new();
                _ = trie.ins(key1(), entry1);
                _ = trie.ins(key2(), entry2);

                _ = trie.track(key1(), TraStrain::TraEmp);

                let mut en_esc = false;
                assert_eq!(entry1, trie.rem_actual(&mut en_esc));
                assert_eq!(Err(KeyErr::Unknown), trie.acq(key1()));
                assert_eq!(Ok(&entry2), trie.acq(key2()));
                assert_eq!(false, en_esc);
            }

            #[test]
            fn one_letter_c() {
                let key1 = || "a".chars();
                let key2 = || "al".chars();

                let entry1 = 50;
                let entry2 = 60;

                let mut trie = Trie::new();
                _ = trie.ins(key1(), entry1);
                _ = trie.ins(key2(), entry2);

                _ = trie.track(key1(), TraStrain::TraEmp);

                let mut en_esc = false;
                assert_eq!(entry1, trie.rem_actual(&mut en_esc));
                assert_eq!(Err(KeyErr::Unknown), trie.acq(key1()));
                assert_eq!(Ok(&entry2), trie.acq(key2()));
                assert_eq!(false, en_esc);
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

                _ = trie.track(key_1(), TraStrain::TraEmp);

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

                _ = trie.track(inner(), TraStrain::TraEmp);

                assert_eq!(inner_entry, trie.rem_actual(&mut false));

                assert_eq!(Err(KeyErr::Unknown), trie.acq(inner()));
                assert_eq!(Ok(&outer_entry), trie.acq(outer()));
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

                _ = trie.track(test(), TraStrain::TraEmp);

                let mut en_esc = false;
                assert_eq!(test_entry, trie.rem_actual(&mut en_esc));
                assert_eq!(false, en_esc);

                assert_eq!(Err(KeyErr::Unknown), trie.acq(test()));
                assert_eq!(Ok(&peer_entry), trie.acq(peer()));
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

                _ = trie.track(test(), TraStrain::TraEmp);

                let mut en_esc = false;
                assert_eq!(test_entry, trie.rem_actual(&mut en_esc));
                assert_eq!(false, en_esc);

                assert_eq!(Err(KeyErr::Unknown), trie.acq(test()));
                assert_eq!(Ok(&peer_entry), trie.acq(peer()));
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

                _ = trie.track(under(), TraStrain::TraEmp);

                let mut en_esc = false;
                assert_eq!(under_entry, trie.rem_actual(&mut en_esc));
                assert_eq!(true, en_esc);

                assert_eq!(Err(KeyErr::Unknown), trie.acq(under()));
                assert_eq!(Ok(&above_entry), trie.acq(above()));

                let res = trie.track(above(), TraStrain::NonRef);
                if let TraRes::OkRef(l) = res {
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
                let trie = Trie::<usize>::new();
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

                if let TraRes::OkRef(l) = res {
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
                _ = trie.track(key(), TraStrain::TraEmp);

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
            fn ok() {
                let key = || "wordbook".chars();

                let mut trie = Trie::<usize>::new();
                _ = trie.ins(key(), 0);
                let res = trie.track(key(), TraStrain::NonEmp);

                match res {
                    TraRes::Ok => {}
                    _ => panic!("Not `TraRes::Ok`, but {:?}.", res),
                }
            }

            #[test]
            fn ok_ref() {
                let key = || "wordbook".chars();
                let entry = 444;

                let mut trie = Trie::<usize>::new();
                _ = trie.ins(key(), entry);
                let res = trie.track(key(), TraStrain::NonRef);

                match res {
                    TraRes::OkRef(l) => assert_eq!(Some(entry), l.en),
                    _ => panic!("Not `TraRes::OkRef(_)`, but {:?}.", res),
                }
            }

            #[test]
            fn ok_mut() {
                let key = || "wordbook".chars();
                let entry = 444;

                let mut trie = Trie::<usize>::new();
                _ = trie.ins(key(), entry);
                let res = trie.track(key(), TraStrain::NonMut);

                match res {
                    TraRes::OkMut(l) => assert_eq!(Some(entry), l.en),
                    _ => panic!("Not `TraRes::OkMut(_)`, but {:?}.", res),
                }
            }

            #[test]
            #[should_panic(expected = "Unsupported result scenario.")]
            fn unsupported_result() {
                let key = || "wordbook".chars();

                let mut trie = Trie::<usize>::new();
                _ = trie.ins(key(), 0);

                _ = trie.track(key(), TraStrain::Unset);
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
            use crate::{KeyErr, Trie};

            #[test]
            fn basic_test() {
                let proof = vec![
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

                let p_len = proof.len();

                let mut trie = Trie::new();
                for p in proof.iter() {
                    _ = trie.ins(p.0.chars(), p.1);
                }

                let ext = trie.ext();
                assert_eq!(true, ext.is_some());
                let ext = ext.unwrap();

                assert_eq!(p_len, ext.len());
                assert_eq!(proof, ext);
                assert_eq!(true, ext.capacity() >= p_len);

                for p in proof.iter() {
                    assert_eq!(Err(KeyErr::Unknown), trie.acq(p.0.chars()));
                }
            }

            #[test]
            #[should_panic(
                expected = "This method is unsupported when `new_with` `re` parameter is provided with `None`."
            )]
            fn re_not_provided() {
                _ = Trie::<usize>::new_with(ix, None, 0).ext()
            }

            #[test]
            fn empty_tree() {
                let mut trie = Trie::<usize>::new();
                assert_eq!(None, trie.ext());
            }
        }

        mod vals {
            use crate::Trie;

            #[test]
            fn basic_test() {
                let proof = [
                    ("aa", 13),
                    ("azbq", 11),
                    ("by", 329),
                    ("ybc", 7),
                    ("ybxr", 53),
                    ("ybxrqutmop", 33),
                    ("ybxrqutmopfvb", 99),
                    ("ybxrqutmoprfg", 80),
                    ("zazazazazabyyb", 55),
                ];

                let p_len = proof.len();

                let mut trie = Trie::new();
                for p in proof.iter() {
                    _ = trie.ins(p.0.chars(), p.1);
                }

                let vals = trie.vals();
                assert_eq!(true, vals.is_some());
                let vals = vals.unwrap();

                assert_eq!(p_len, vals.len());

                for zip in proof.iter().zip(vals.iter()) {
                    assert_eq!(zip.0 .1, *zip.1);
                }

                assert_eq!(true, vals.capacity() >= p_len);

                for p in proof.iter() {
                    assert_eq!(Ok(&p.1), trie.acq(p.0.chars()));
                }
            }

            #[test]
            fn empty_tree() {
                let trie = Trie::<usize>::new();
                assert_eq!(None, trie.vals());
            }
        }

        mod keys {
            use crate::english_letters::ix;
            use crate::Trie;

            #[test]
            fn basic_test() {
                let proof = vec![
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

                let p_len = proof.len();

                let mut trie = Trie::new();
                for p in proof.iter() {
                    _ = trie.ins(p.0.chars(), p.1);
                }

                let keys = trie.keys();
                assert_eq!(true, keys.is_some());
                let keys = keys.unwrap();

                assert_eq!(p_len, keys.len());

                for zip in proof.iter().zip(keys.iter()) {
                    assert_eq!(zip.0 .0, *zip.1);
                }

                assert_eq!(true, keys.capacity() >= p_len);

                for p in proof.iter() {
                    assert_eq!(Ok(&p.1), trie.acq(p.0.chars()));
                }
            }

            #[test]
            #[should_panic(
                expected = "This method is unsupported when `new_with` `re` parameter is provided with `None`."
            )]
            fn re_not_provided() {
                _ = Trie::<usize>::new_with(ix, None, 0).keys()
            }

            #[test]
            fn empty_tree() {
                let trie = Trie::<usize>::new();
                assert_eq!(None, trie.keys());
            }
        }

        mod view {
            use crate::english_letters::ix;
            use crate::Trie;

            #[test]
            fn basic_test() {
                let proof = vec![
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

                let p_len = proof.len();

                let mut trie = Trie::new();
                for p in proof.iter() {
                    _ = trie.ins(p.0.chars(), *p.1);
                }

                let view = trie.view();
                assert_eq!(true, view.is_some());
                let view = view.unwrap();

                assert_eq!(p_len, view.len());
                assert_eq!(proof, view);
                assert_eq!(true, view.capacity() >= p_len);

                for p in proof.iter() {
                    assert_eq!(Ok(p.1), trie.acq(p.0.chars()));
                }
            }

            #[test]
            #[should_panic(
                expected = "This method is unsupported when `new_with` `re` parameter is provided with `None`."
            )]
            fn re_not_provided() {
                _ = Trie::<usize>::new_with(ix, None, 0).view()
            }

            #[test]
            fn empty_tree() {
                let trie = Trie::<usize>::new();
                assert_eq!(None, trie.view());
            }
        }

        use crate::KeyErr;

        #[test]
        fn clr() {
            let key = || "abc".chars();

            let mut trie = Trie::<usize>::new();
            _ = trie.ins(key(), 99);
            assert_eq!(1, trie.clr());

            assert_eq!(Err(KeyErr::Unknown), trie.acq(key()));
            assert_eq!(ab(ALPHABET_LEN), trie.rt);
            assert_eq!(0, trie.ct);
        }

        #[test]
        fn ct() {
            let test = 3;
            let mut trie = Trie::<usize>::new();
            assert_eq!(0, trie.ct());
            trie.ct = test;
            assert_eq!(test, trie.ct());
        }

        use crate::aide::address;

        #[test]
        fn as_ref() {
            let trie = Trie::<usize>::new();

            let as_ref = address(trie.as_ref());
            let proof = address(&trie.rt);

            assert_eq!(as_ref, proof);
        }

        #[test]
        fn as_mut() {
            let mut trie = Trie::<usize>::new();

            let as_mut = address(trie.as_mut());
            let proof = address(&trie.rt);

            assert_eq!(as_mut, proof);
        }
    }
}

// cargo fmt && cargo test --features test-ext --release
// cargo fmt && cargo test --release
