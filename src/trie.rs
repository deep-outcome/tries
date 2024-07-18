#[no_std]

type Alphabet<T> = Box<[Letter<T>]>;
type Path<'a, T> = Vec<&'a Letter<T>>;

const ALPHABET_LEN: usize = 26;

fn alphabet<T>() -> Alphabet<T> {
    let mut vec = Vec::with_capacity(ALPHABET_LEN);

    #[cfg(test)]
    let mut c = 'a' as u8;
    for sc in vec.spare_capacity_mut() {
        let mut _letter = sc.write(Letter::new());
        #[cfg(test)]
        {
            _letter.value = c as char;
            c = c + 1;
        }
    }

    unsafe { vec.set_len(ALPHABET_LEN) };
    vec.into_boxed_slice()
}

fn entry_letter<'a, T>(path: &Path<'a, T>, key: &Key) -> Option<&'a Letter<T>> {
    let el_ix = key.key.len() - 1;

    if path.len() - 1 < el_ix {
        None
    } else {
        let el = path[el_ix];
        if el.entry() {
            Some(el)
        } else {
            None
        }
    }
}

fn ix(c: char) -> usize {
    c as usize - 'a' as usize
}

pub struct Key {
    key: String,
}

impl Key {
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

#[cfg_attr(test, derive(Debug, PartialEq))]
pub enum KeyError {
    KeyWithInvalidChars,
    KeyWithInvalidLength,
}

pub struct Trie<T> {
    root: Alphabet<T>,
}

impl<T> Trie<T> {
    pub fn new() -> Trie<T> {
        Trie {
            root: crate::alphabet::<T>(),
        }
    }

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

    pub fn member(&self, key: &Key) -> Option<&T> {
        let path = self.path(key);

        let el = entry_letter(&path, key);

        if let Some(el) = el {
            el.entry.as_ref()
        } else {
            None
        }
    }

    pub fn delete(&mut self, key: &Key) -> Result<(), ()> {
        let path = self.path(key);
        let entry_l = entry_letter(&path, key);

        let entry_l = if let Some(el) = entry_l {
            el
        } else {
            return Err(());
        };

        unsafe { as_mut(entry_l) }.entry = None;

        if entry_l.alphabet() {
            return Ok(());
        }

        let mut rev = path.iter().rev();
        _ = rev.next();

        while let Some(l) = rev.next() {
            let l_mut = unsafe { as_mut(*l) };

            let alphabet = l_mut.alphabet.as_ref().unwrap();
            let mut remove_alphab = true;

            for inx in 0..ALPHABET_LEN {
                let letter = &alphabet[inx];

                if letter.alphabet() || letter.entry() {
                    remove_alphab = false;
                    break;
                }
            }

            if remove_alphab {
                l_mut.alphabet = None;
            } else {
                break;
            }

            if l.entry() {
                break;
            }
        }

        return Ok(());

        unsafe fn as_mut<T>(letter: &Letter<T>) -> &mut Letter<T> {
            let ptr: *const Letter<T> = letter;
            let mut_ptr: *mut Letter<T> = std::mem::transmute(ptr);
            mut_ptr.as_mut().unwrap()
        }
    }

    fn path(&self, key: &Key) -> Vec<&Letter<T>> {
        let key = &key.key;

        let mut alphabet = &self.root;
        let entryl_ix = key.len() - 1;

        let mut path = Vec::with_capacity(entryl_ix + 1);
        let mut erator = key.chars().enumerate();

        loop {
            let (it_ix, c) = erator.next().unwrap();

            let ix = ix(c);

            let letter = &alphabet[ix];
            path.push(letter);

            if it_ix < entryl_ix {
                if !letter.alphabet() {
                    break;
                }
            } else {
                break;
            }

            alphabet = letter.alphabet.as_ref().unwrap();
        }

        return path;
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
        let ab = alphabet_fn::<usize>();
        assert_eq!(crate::ALPHABET_LEN, ab.len());

        for (ix, c) in ('a'..='z').enumerate() {
            let letter = &ab[ix];
            assert_eq!(c, letter.value);
            assert!(letter.alphabet.is_none());
            assert!(letter.entry.is_none());
        }
    }

    mod entry_letter {
        use crate::{entry_letter, Key, Letter};

        #[test]
        fn longer_key() {
            let letter: Letter<usize> = Letter {
                value: 'a',
                alphabet: None,
                entry: None,
            };
            let path = vec![&letter; 3];
            let key = Key {
                key: String::from("aaaa"),
            };

            assert_eq!(None, entry_letter(&path, &key));
        }

        #[test]
        fn not_entry() {
            let letter: Letter<usize> = Letter {
                value: 'a',
                alphabet: None,
                entry: None,
            };
            let path = vec![&letter; 4];
            let key = Key {
                key: String::from("aaaa"),
            };

            assert_eq!(None, entry_letter(&path, &key));
        }

        #[test]
        fn entry() {
            let undistinctive: Letter<usize> = Letter {
                value: 'a',
                alphabet: None,
                entry: None,
            };

            let mut distinctive = undistinctive.clone();
            distinctive.entry = Some(0);
            distinctive.value = 'b';

            let mut path = vec![&undistinctive; 3];
            path.push(&distinctive);

            let key = Key {
                key: String::from("aaab"),
            };

            let el = entry_letter(&path, &key);
            assert!(el.is_some());
            let el = el.unwrap();
            assert!(el.entry());
            assert_eq!('b', el.value);
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
    }

    mod trie {
        use crate::{alphabet, Trie};

        #[test]
        fn new() {
            let trie = Trie::<usize>::new();

            let ab = alphabet();
            let rt = trie.root;

            assert_eq!(*ab, *rt);
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

        /// Letter in path to entry being deleted
        /// cannot be deleted if and only if participates
        /// in path to another entry. Path len varies 0…m.
        mod delete {

            use crate::{ix, Key, Trie};

            #[test]
            fn basic_test() {
                let key = Key::new("Keyword").unwrap();
                let mut trie = Trie::new();
                trie.insert(0usize, &key);

                assert!(trie.delete(&key).is_ok());

                let k = &trie.root[ix('k')];
                assert!(!k.alphabet());
            }

            #[test]
            fn not_member() {
                let key = Key::new("Keyword").unwrap();
                let mut trie = Trie::new();
                trie.insert(0usize, &key);

                for k in ["Key", "Opener"] {
                    let bad_key = Key::new(k).unwrap();
                    let err = trie.delete(&bad_key);
                    assert!(err.is_err());
                    assert!(trie.member(&key).is_some());
                }
            }

            #[test]
            fn inner_entry() {
                let mut trie = Trie::new();

                let outer = Key::new("Keyword").unwrap();
                trie.insert(0usize, &outer);

                let inner = Key::new("Key").unwrap();
                trie.insert(0usize, &inner);

                assert!(trie.delete(&inner).is_ok());
                assert!(trie.member(&inner).is_none());
                assert!(trie.member(&outer).is_some());
            }

            #[test]
            fn entry_with_peer_entry() {
                let mut trie = Trie::new();

                let peer = Key::new("Keyworder").unwrap();
                trie.insert(0usize, &peer);

                let test = Key::new("Keywordee").unwrap();
                trie.insert(0usize, &test);

                assert!(trie.delete(&test).is_ok());
                assert!(trie.member(&test).is_none());

                let path = trie.path(&test);
                assert_eq!(test.key.len(), path.len());
            }

            #[test]
            fn entry_with_peer_with_alphabet() {
                let mut trie = Trie::new();

                let peer = Key::new("Keyworders").unwrap();
                trie.insert(0usize, &peer);

                let test = Key::new("Keywordee").unwrap();
                trie.insert(0usize, &test);

                assert!(trie.delete(&test).is_ok());
                assert!(trie.member(&test).is_none());

                let path = trie.path(&test);
                assert_eq!(test.key.len(), path.len());

                assert!(trie.member(&peer).is_some());
            }

            #[test]
            fn entry_under_entry() {
                let mut trie = Trie::new();

                let above = Key::new("Keyworder").unwrap();
                trie.insert(0usize, &above);

                let under = Key::new("Keyworders").unwrap();
                trie.insert(0usize, &under);

                assert!(trie.delete(&under).is_ok());
                assert!(trie.member(&under).is_none());
                assert!(trie.member(&above).is_some());

                let path = trie.path(&under);

                let r_letter = &path[path.len() - 1];
                assert_eq!('r', r_letter.value);
                assert!(!r_letter.alphabet());
            }
        }

        mod path {

            use crate::{Key, Trie};

            #[test]
            fn path() {
                let key = Key::new("keyword").unwrap();
                let mut trie = Trie::new();
                trie.insert(33usize, &key);

                let path = trie.path(&key);

                let key = key.key;
                let key_len = key.len();

                assert_eq!(key_len, path.len());
                for (c, l) in key.chars().zip(path.iter()) {
                    assert_eq!(c, l.value);
                }

                let entry_l = path[key_len - 1];
                assert!(entry_l.entry());
                assert_eq!(33, entry_l.entry.unwrap());
            }

            #[test]
            fn unknown_key() {
                let key = Key::new("Key").unwrap();
                let trie = Trie::<usize>::new();

                let path = trie.path(&key);
                assert_eq!(1, path.len());
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
