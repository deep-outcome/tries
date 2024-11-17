//! Classic retrieval tree implementation with fixed size alphabet per node.

type Alphabet<T> = Box<[Letter<T>]>;

const ALPHABET_LEN: usize = 26;

#[cfg_attr(test, derive(PartialEq, Debug))]
enum TraRes<'a, T> {
    Ok(&'a Letter<T>),
    Unknown,
}

fn alphabet<T>() -> Alphabet<T> {
    let mut alphabet = Vec::new();
    alphabet.reserve_exact(ALPHABET_LEN);

    #[cfg(test)]
    let mut c = 'a' as u8;
    for sc in alphabet.spare_capacity_mut() {
        let mut _letter = sc.write(Letter::new());
        #[cfg(test)]
        {
            _letter.value = c as char;
            c = c + 1;
        }
    }

    unsafe { alphabet.set_len(ALPHABET_LEN) };
    alphabet.into_boxed_slice()
}

fn ix(c: char) -> usize {
    c as usize - 'a' as usize
}

/// String key validated for usage with `Trie`.
pub struct Key {
    key: String,
}

impl Key {
    /// All capitals are lowercased. English alphabet only.
    ///
    /// `KeyError` if `s` is unusable as key.
    pub fn new(s: &str) -> Result<Key, KeyError> {
        if s.len() == 0 {
            return Err(KeyError::KeyWithInvalidLength);
        }

        let mut key = String::with_capacity(s.len());
        for mut c in s.chars() {
            if c.is_ascii_alphabetic() {
                if c.is_ascii_uppercase() {
                    c.make_ascii_lowercase();
                }

                key.push(c);
            } else {
                return Err(KeyError::KeyWithInvalidChars);
            };
        }

        Ok(Key { key })
    }
}

impl std::ops::Deref for Key {
    type Target = str;

    /// Returns `&str` of key string.
    fn deref(&self) -> &str {
        &self.key
    }
}

/// Invalid options of key.
#[derive(Debug, PartialEq)]
pub enum KeyError {
    /// Other than A–Za–z.
    KeyWithInvalidChars,
    /// Zero-length key.
    KeyWithInvalidLength,
}

/// Trie implementation allowing for mapping any `T` to string.
///
/// Capitals are lowercased.
///
/// ± all methods with classic trie ACC (asymptotic computational complexity):
/// - _s_ means `char`s iterated over.
/// - _q_ means unique nodes.
/// ```rust
/// use plain_trie::{Key, Trie};
/// let key = Key::new("touchstone").unwrap();
///
/// let mut trie = Trie::new();
/// trie.insert(3usize, &key);
///
/// assert!(trie.member(&key).is_some());
/// ```
pub struct Trie<T> {
    root: Alphabet<T>,
    trac: Vec<*mut Letter<T>>,
}

impl<T> Trie<T> {
    /// Ctor.
    pub fn new() -> Trie<T> {
        Trie {
            root: crate::alphabet::<T>(),
            trac: Vec::new(),
        }
    }

    /// ACC:
    /// - time scope is Θ(s)
    /// - space scope is Θ(q)
    pub fn insert(&mut self, entry: T, key: &Key) {
        let key = &key.key;
        let last_letter_ix = key.len() - 1;
        let mut alphabet = &mut self.root;

        let mut erator = key.chars().enumerate();

        loop {
            let (it_ix, c) = erator.next().unwrap();
            let c_ix = ix(c);

            let letter = &mut alphabet[c_ix];
            if it_ix < last_letter_ix {
                if !letter.alphabet() {
                    letter.alphabet = Some(crate::alphabet())
                }
            } else {
                letter.entry = Some(entry);
                break;
            }

            alphabet = letter.alphabet.as_mut().unwrap();
        }
    }

    /// `None` for unknown key.
    ///
    /// ACC time scope is Θ(s)
    pub fn member(&self, key: &Key) -> Option<&T> {
        let this = unsafe { self.as_mut() };

        let track_res = this.track(key, false);
        if let TraRes::Ok(l) = track_res {
            let as_ref = l.entry.as_ref();
            Some(unsafe { as_ref.unwrap_unchecked() })
        } else {
            None
        }
    }

    unsafe fn as_mut(&self) -> &mut Self {
        let ptr: *const Self = self;
        let mut_ptr: *mut Self = core::mem::transmute(ptr);
        mut_ptr.as_mut().unwrap()
    }

    /// `Err` for unknown key.
    ///
    /// ACC TS is backtracing buffer capacity dependent:
    /// - time scope: Ω(s) or ϴ(s)
    /// - space scope: ϴ(s)
    pub fn delete(&mut self, key: &Key) -> Result<(), ()> {
        let track_res = self.track(&key, true);
        let res = if let TraRes::Ok(_) = track_res {
            Self::delete_actual(&mut self.trac);
            Ok(())
        } else {
            Err(())
        };

        self.trac.clear();
        res
    }

    fn delete_actual(trac: &mut Vec<*mut Letter<T>>) {
        let mut trace = trac.iter_mut().map(|x| unsafe { x.as_mut() }.unwrap());
        let entry_node = trace.next_back().unwrap();

        entry_node.entry = None;

        if entry_node.alphabet() {
            return;
        }

        while let Some(l) = trace.next_back() {
            let alphabet = l.alphabet.as_ref().unwrap();
            let mut remove_alphab = true;

            for ix in 0..ALPHABET_LEN {
                let letter = &alphabet[ix];

                if letter.alphabet() || letter.entry() {
                    remove_alphab = false;
                    break;
                }
            }

            if remove_alphab {
                l.alphabet = None;
            } else {
                break;
            }

            if l.entry() {
                break;
            }
        }
    }

    /// `Trie` uses internal buffer, to avoid excesive allocations and copying, which grows
    /// over time due backtracing in `delete` method which backtraces whole path from entry
    /// node to root node.
    ///
    /// Use this method to shrink or extend it to fit actual program needs. Neither shrinking nor extending
    /// is guaranteed to be exact. See `Vec::with_capacity()` and `Vec::reserve()`. For optimal `delete` performance, set `approx_cap` to _key_ `char` length.
    ///
    /// Some high value is sufficient anyway. Since buffer continuous
    /// usage, its capacity will likely expand at some point in time to size sufficient to all keys.
    ///
    /// Return value is actual buffer capacity.
    ///
    /// **Note:** While `String` is UTF8 encoded, its byte length does not have to equal its `char` count
    /// which is either equal or lesser.
    /// ```
    /// let sights = "🤩";
    /// assert_eq!(4, sights.len());
    /// assert_eq!(1, sights.chars().count());
    ///
    /// let yes = "sí";
    /// assert_eq!(3, yes.len());
    /// assert_eq!(2, yes.chars().nth(1).unwrap().len_utf8());
    ///
    /// let abc = "abc";
    /// assert_eq!(3, abc.len());
    /// ```
    pub fn put_trace_cap(&mut self, approx_cap: usize) -> usize {
        let trac = &mut self.trac;
        let cp = trac.capacity();

        if cp < approx_cap {
            trac.reserve(approx_cap);
        } else if cp > approx_cap {
            *trac = Vec::with_capacity(approx_cap);
        }

        trac.capacity()
    }

    /// Return value is internal backtracing buffer capacity.
    ///
    /// Check with `fn put_trace_cap` for details.
    pub fn acq_trace_cap(&self) -> usize {
        self.trac.capacity()
    }

    // - TS: Ω(s) when `tracing = true`, ϴ(s) otherwise
    // - SS: ϴ(s) when `tracing = true`, ϴ(0) otherwise
    fn track(&mut self, key: &Key, tracing: bool) -> TraRes<T> {
        let mut key = key.key.chars();

        let c = key.next();
        let c = unsafe { c.unwrap_unchecked() };

        let trac = &mut self.trac;
        let mut letter = &mut self.root[ix(c)];

        loop {
            if tracing {
                trac.push(letter)
            }

            if let Some(c) = key.next() {
                if let Some(ab) = letter.alphabet.as_mut() {
                    letter = &mut ab[ix(c)];
                } else {
                    return TraRes::Unknown;
                }
            } else {
                break;
            }
        }

        if letter.entry() {
            TraRes::Ok(letter)
        } else {
            TraRes::Unknown
        }
    }
}

#[cfg_attr(test, derive(PartialEq, Clone))]
struct Letter<T> {
    #[cfg(test)]
    value: char,
    alphabet: Option<Alphabet<T>>,
    entry: Option<T>,
}

impl<T> Letter<T> {
    fn entry(&self) -> bool {
        self.entry.is_some()
    }

    fn alphabet(&self) -> bool {
        self.alphabet.is_some()
    }

    fn new() -> Self {
        Letter {
            #[cfg(test)]
            value: '🫀',
            alphabet: None,
            entry: None,
        }
    }
}

#[cfg(test)]
use std::fmt::{Debug, Formatter};

#[cfg(test)]
impl<T> Debug for Letter<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let alphabet = if self.alphabet() { "Alphabet" } else { "None" };

        f.write_fmt(format_args!(
            "Letter {{\n  value: {:?}\n  alphabet: {:?}\n  entry: {:?}\n}}",
            self.value, alphabet, self.entry
        ))
    }
}

#[cfg(test)]
mod tests_of_units {

    fn unsupported_chars() -> [u8; 4] {
        #[rustfmt::skip] let ucs =
        [
            'a' as u8 -1, 'z' as u8 +1,
            'A' as u8 -1, 'Z' as u8 +1,
        ];
        ucs
    }

    use super::{alphabet as alphabet_fn, ix};

    #[test]
    fn alphabet() {
        let alphabet = alphabet_fn::<usize>();
        assert_eq!(crate::ALPHABET_LEN, alphabet.len());

        for (ix, c) in ('a'..='z').enumerate() {
            let letter = &alphabet[ix];
            assert_eq!(c, letter.value);
            assert!(letter.alphabet.is_none());
            assert!(letter.entry.is_none());
        }
    }

    #[test]
    fn ix_test() {
        let ix = ix('a');
        assert_eq!(0, ix);
    }

    mod key {

        use super::unsupported_chars;
        use crate::{Key, KeyError, ALPHABET_LEN};

        #[test]
        fn zero_len() {
            let key = Key::new("");

            assert!(key.is_err());
            assert_eq!(KeyError::KeyWithInvalidLength, key.err().unwrap());
        }

        #[test]
        fn invalid_str() {
            let ucs = unsupported_chars();

            let mut s = String::new();
            for c in ucs {
                s.push(c as char);
                let key = Key::new(&s);
                assert!(key.is_err());
                assert_eq!(KeyError::KeyWithInvalidChars, key.err().unwrap());
                s.clear();
            }
        }

        #[test]
        fn valid_str() {
            let mut s = String::with_capacity(ALPHABET_LEN * 2);
            for c in ('a'..='z').zip('A'..='Z') {
                s.push(c.0);
                s.push(c.1);
            }

            let key = Key::new(&s);
            assert!(key.is_ok());

            let proof = "aabbccddeeffgghhiijjkkllmmnnooppqqrrssttuuvvwwxxyyzz";

            assert_eq!(proof, key.unwrap().key);
        }

        use std::ops::Deref;
        #[test]
        fn deref() {
            let test = "test";
            let key = Key::new(&test).unwrap();

            assert_eq!(test, key.deref());
        }
    }

    mod trie {
        use crate::{alphabet, Trie};

        #[test]
        fn new() {
            let trie = Trie::<usize>::new();

            let alphabet = alphabet();
            let rt = trie.root;

            assert_eq!(*alphabet, *rt);
        }

        mod insert {
            use crate::{ix as ix_fn, Key, Trie};

            #[test]
            fn basic_test() {
                const KEY: &str = "touchstone";
                let key = Key::new(&KEY).unwrap();

                let mut trie = Trie::new();
                trie.insert(3usize, &key);

                let last_letter_ix = KEY.len() - 1;

                let mut alphabet = &trie.root;

                for (ix, c) in KEY.chars().enumerate() {
                    let letter = &alphabet[ix_fn(c)];

                    if ix < last_letter_ix {
                        let temp = &letter.alphabet;
                        assert!(temp.is_some());
                        alphabet = temp.as_ref().unwrap();
                    } else {
                        assert!(!letter.alphabet());

                        let entry = letter.entry;
                        assert!(entry.is_some());
                        assert_eq!(3usize, entry.unwrap());
                    }
                }
            }

            #[test]
            fn existing_path_insert() {
                let existing = Key::new("touchstone").unwrap();
                let new = Key::new("touch").unwrap();

                let mut trie = Trie::new();
                trie.insert(3usize, &existing);
                trie.insert(4usize, &new);

                assert!(trie.member(&existing).is_some());
                assert!(trie.member(&new).is_some());
            }

            #[test]
            fn overwrite() {
                let key = Key::new("touchstone").unwrap();

                let mut trie = Trie::new();
                trie.insert(3usize, &key);
                trie.insert(4, &key);

                let member = trie.member(&key);
                assert!(member.is_some());
                assert_eq!(4, *member.unwrap());
            }
        }

        mod member {

            use crate::{Key, Trie};

            #[test]
            fn member() {
                let key = Key::new("Keyword").unwrap();
                let mut trie = Trie::new();
                trie.insert(27usize, &key);

                let member = trie.member(&key);
                assert!(member.is_some());
                assert_eq!(27, *member.unwrap());
            }

            #[test]
            fn not_member() {
                let key = Key::new("Keyword").unwrap();
                let mut trie = Trie::new();
                trie.insert(0usize, &key);

                for k in ["Key", "Opener"] {
                    let key = Key::new(k).unwrap();
                    let member = trie.member(&key);
                    assert!(member.is_none());
                }
            }
        }

        #[test]
        fn as_mut() {
            let trie = Trie::<usize>::new();
            let trie_ptr = &trie as *const Trie<usize>;
            let trie_mut = unsafe { trie.as_mut() };
            assert_eq!(trie_ptr as usize, trie_mut as *mut Trie<usize> as usize);
        }

        /// Letter in path to entry being deleted
        /// cannot be deleted if and only if participates
        /// in path to another entry. Path len varies 0…m.
        mod delete {
            use crate::{Key, Trie};

            #[test]
            fn known_unknown() {
                let known = Key::new("VigilantAndVigourous").unwrap();
                let unknown = Key::new("NeglectfulAndFeeble").unwrap();

                let mut trie = Trie::new();
                trie.insert(3, &known);

                assert_eq!(Ok(()), trie.delete(&known));
                assert_eq!(None, trie.member(&known));
                assert_eq!(0, trie.trac.len());

                assert_eq!(Err(()), trie.delete(&unknown));
                assert_eq!(0, trie.trac.len());
            }
        }

        mod delete_actual {
            use crate::{ix, Key, TraRes, Trie};

            #[test]
            fn basic_test() {
                let key = Key::new("Keyword").unwrap();
                let mut trie = Trie::new();

                trie.insert(3, &key);

                _ = trie.track(&key, true);
                Trie::delete_actual(&mut trie.trac);

                let k = &trie.root[ix('k')];
                assert_eq!(false, k.alphabet());
            }

            #[test]
            fn inner_entry() {
                let mut trie = Trie::new();

                let outer_val = 3;
                let outer = Key::new("Keyword").unwrap();
                trie.insert(outer_val, &outer);

                let inner_val = 8;
                let inner = Key::new("Key").unwrap();
                trie.insert(inner_val, &inner);

                _ = trie.track(&inner, true);
                Trie::delete_actual(&mut trie.trac);

                assert_eq!(None, trie.member(&inner));
                assert_eq!(Some(&outer_val), trie.member(&outer));
            }

            #[test]
            fn entry_with_peer_entry() {
                let mut trie = Trie::new();

                let peer_val = 3;
                let peer = Key::new("Keyworder").unwrap();
                trie.insert(peer_val, &peer);

                let test_val = 8;
                let test = Key::new("Keywordee").unwrap();
                trie.insert(test_val, &test);

                _ = trie.track(&test, true);
                Trie::delete_actual(&mut trie.trac);

                assert_eq!(None, trie.member(&test));
                assert_eq!(Some(&peer_val), trie.member(&peer));
            }

            #[test]
            fn entry_with_peer_with_alphabet() {
                let mut trie = Trie::new();

                let peer_val = 3;
                let peer = Key::new("Keyworders").unwrap();
                trie.insert(peer_val, &peer);

                let test_val = 8;
                let test = Key::new("Keywordee").unwrap();
                trie.insert(test_val, &test);

                _ = trie.track(&test, true);
                Trie::delete_actual(&mut trie.trac);

                assert_eq!(None, trie.member(&test));
                assert_eq!(Some(&peer_val), trie.member(&peer));
            }

            #[test]
            fn entry_under_entry() {
                let mut trie = Trie::new();

                let above_val = 3;
                let above = Key::new("Keyworder").unwrap();
                trie.insert(above_val, &above);

                let under_val = 8;
                let under = Key::new("Keyworders").unwrap();
                trie.insert(under_val, &under);

                _ = trie.track(&under, true);

                Trie::delete_actual(&mut trie.trac);
                assert_eq!(None, trie.member(&under));
                assert_eq!(Some(&above_val), trie.member(&above));

                let res = trie.track(&above, false);
                if let TraRes::Ok(l) = res {
                    assert_eq!('r', l.value);
                    assert_eq!(false, l.alphabet());
                } else {
                    panic!("TraRes::Ok(_) was expected, instead {:?}.", res);
                }
            }
        }
        mod put_trace_cap {
            use crate::Trie;

            #[test]
            fn extend() {
                const NEW_CAP: usize = 10;

                let mut trie = Trie::<usize>::new();
                assert!(trie.trac.capacity() < NEW_CAP);

                let size = trie.put_trace_cap(NEW_CAP);
                assert!(size >= NEW_CAP);
                assert!(trie.trac.capacity() >= NEW_CAP);
            }

            #[test]
            fn shrink() {
                const NEW_CAP: usize = 10;
                const OLD_CAP: usize = 50;

                let mut trie = Trie::<usize>::new();
                trie.trac = Vec::with_capacity(OLD_CAP);

                let size = trie.put_trace_cap(NEW_CAP);
                assert!(size >= NEW_CAP && size < OLD_CAP);
                let cap = trie.trac.capacity();
                assert!(cap >= NEW_CAP && cap < OLD_CAP);
            }

            #[test]
            fn same() {
                let mut trie = Trie::<usize>::new();
                let cap = trie.trac.capacity();

                let size = trie.put_trace_cap(cap);
                assert_eq!(cap, size);
                assert_eq!(cap, trie.trac.capacity());
            }
        }

        #[test]
        fn acq_trace_cap() {
            const VAL: usize = 10;

            let mut trie = Trie::<usize>::new();
            let trac = &mut trie.trac;

            assert!(trac.capacity() < VAL);
            trac.reserve_exact(VAL);
            assert_eq!(VAL, trie.acq_trace_cap());
        }

        mod track {
            use crate::{Key, TraRes, Trie};

            #[test]
            fn singular_key() {
                let key = Key::new("A").unwrap();

                let mut trie = Trie::new();

                let val = 8;
                trie.insert(val, &key);
                let res = trie.track(&key, true);

                if let TraRes::Ok(l) = res {
                    let l_val = l.value;
                    let trac = &trie.trac;

                    assert_eq!('a', l_val);
                    assert_eq!(1, trac.len());

                    let l = unsafe { trac[0].as_ref() }.unwrap();
                    assert_eq!('a', l.value)
                } else {
                    panic!("TraRes::Ok(_) was expected, instead {:?}.", res);
                }
            }

            #[test]
            fn tracing() {
                let key = Key::new("DictionaryLexicon").unwrap();

                let mut trie = Trie::new();

                let val = 8;
                trie.insert(val, &key);
                _ = trie.track(&key, true);

                let proof = key.key;
                let trac = &trie.trac;

                assert_eq!(proof.len(), trac.len());

                for (x, c) in proof.chars().enumerate() {
                    let l = trac[x];
                    let l = unsafe { l.as_mut() }.unwrap();
                    assert_eq!(c, l.value);
                }
            }

            #[test]
            fn unknown_not_path() {
                let key = Key::new("Wordbook").unwrap();
                let bad_key = Key::new("Wordbooks").unwrap();

                let mut trie = Trie::new();

                let val = 8;
                trie.insert(val, &key);
                let res = trie.track(&bad_key, false);
                assert_eq!(TraRes::Unknown, res);
            }

            #[test]
            fn unknown_not_entry() {
                let key = Key::new("Wordbooks").unwrap();
                let bad_key = Key::new("Wordbook").unwrap();

                let mut trie = Trie::new();

                trie.insert(8, &key);
                let res = trie.track(&bad_key, false);
                assert_eq!(TraRes::Unknown, res);
            }
        }
    }

    mod letter {

        use crate::{alphabet as alphabet_fn, Letter};

        #[test]
        fn entry() {
            let mut letter = Letter::<usize>::new();

            assert!(!letter.entry());
            letter.entry = Some(1);
            assert!(letter.entry());
        }

        #[test]
        fn alphabet() {
            let mut letter = Letter::<usize>::new();

            assert!(!letter.alphabet());
            letter.alphabet = Some(alphabet_fn());
            assert!(letter.alphabet());
        }

        #[test]
        fn new() {
            let letter = Letter::<usize>::new();

            assert_eq!('🫀', letter.value);
            assert!(letter.alphabet.is_none());
            assert!(letter.entry.is_none());
        }
    }
}

// cargo test --release
