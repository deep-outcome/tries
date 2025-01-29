//! Dynamic trie in contrast to classic trie does not have fixed size alphabet associated with node.
//!
//! Each node has dynamic alphabet of size as to satisfy exactly associated branches.

use std::collections::hash_map::HashMap;

mod res;
pub use res::{AcqRes, InsRes, KeyErr, RemRes};

type Links<T> = HashMap<char, Node<T>>;

/// Retrieval tree implementation allowing for mapping any `T` to any `impl Iterator<Item = char>` type.
///
/// Node occurs per every `char` as defined by Rust lang and uses `std::collections::HashMap`
/// to linking subnodes. Thus all methods complexity is respective to hashmap methods complexity.
pub struct Trie<T> {
    root: Node<T>,
    // backtrace buff
    btr: Vec<(char, *mut Node<T>)>,
}

const NULL: char = '\0';
impl<T> Trie<T> {
    /// Ctor.
    pub fn new() -> Trie<T> {
        Trie {
            root: Node::<T>::empty(),
            btr: Vec::new(),
        }
    }

    /// Return value is `InsRes::Ok((&mut T, Option<T>))` when operation accomplished. It holds previous
    /// entry, if there was some.
    ///
    /// Only invalid key recognized is zero-length key.
    pub fn ins(&mut self, entry: T, mut key: impl Iterator<Item = char>) -> InsRes<T> {
        let mut next = key.next();

        if next.is_none() {
            return InsRes::Err(KeyErr::ZeroLen);
        }

        let mut node = &mut self.root;
        while let Some(c) = next {
            let links = node.links.get_or_insert_with(|| Links::new());
            node = links.entry(c).or_insert(Node::<T>::empty());

            next = key.next();
        }

        let en = &mut node.entry;
        let prev = en.replace(entry);
        let curr = en.as_mut().unwrap();
        InsRes::Ok((curr, prev))
    }

    /// Acquires reference to entry associted to `key`.
    pub fn acq(&self, key: impl Iterator<Item = char>) -> AcqRes<T> {
        let this = unsafe { self.as_mut() };
        let res = this.track(key, false);

        if let TraRes::Ok(en) = res {
            let en = en.entry.as_ref();
            AcqRes::Ok(unsafe { en.unwrap_unchecked() })
        } else {
            AcqRes::Err(res.key_err())
        }
    }

    unsafe fn as_mut(&self) -> &mut Self {
        let ptr: *const Self = self;
        ptr.cast_mut().as_mut().unwrap()
    }

    /// `Err` for unknown key.
    pub fn delete(&mut self, key: impl Iterator<Item = char>) -> Result<(), ()> {
        let tra_res = self.track(key, true);
        let res = if let TraRes::Ok(_) = tra_res {
            self.delete_actual(
                #[cfg(test)]
                &mut 0,
            );
            Result::Ok(())
        } else {
            Result::Err(())
        };

        self.btr.clear();
        res
    }

    fn delete_actual(&mut self, #[cfg(test)] esc_code: &mut usize) {
        let mut trace = self.btr.iter();
        let en_duo = trace.next_back().unwrap();
        let mut node = unsafe { en_duo.1.as_mut() }.unwrap();

        if node.links() {
            node.entry = None;

            #[cfg(test)]
            {
                *esc_code = 1;
            }

            return;
        }

        // subnode key
        let mut sn_key = en_duo.0;
        while let Some((c, n)) = trace.next_back() {
            node = unsafe { n.as_mut() }.unwrap();
            let links = node.links.as_mut().unwrap();
            _ = links.remove(&sn_key);

            if links.len() > 0 {
                #[cfg(test)]
                {
                    *esc_code = 2;
                }

                return;
            }

            if node.entry() {
                #[cfg(test)]
                {
                    *esc_code = 3;
                }

                break;
            }

            sn_key = *c;
        }

        node.links = None;
        #[cfg(test)]
        {
            if *esc_code != 3 {
                *esc_code = 4;
            }
        }
    }

    // - c is count of `char`s iterated over
    // - TC: Ω(c) when `tracing = true`, ϴ(c) otherwise
    // - SC: ϴ(c) when `tracing = true`, ϴ(0) otherwise
    fn track<'a>(
        &'a mut self,
        mut key: impl Iterator<Item = char>,
        tracing: bool,
    ) -> TraRes<'a, T> {
        let mut next = key.next();

        if next.is_none() {
            return TraRes::ZeroLenKey;
        }

        let mut node = &mut self.root;
        let tr = &mut self.btr;

        if tracing {
            tr.push((NULL, node));
        }

        while let Some(c) = next {
            next = key.next();

            if let Some(l) = node.links.as_mut() {
                if let Some(n) = l.get_mut(&c) {
                    if tracing {
                        tr.push((c, n));
                    }

                    node = n;
                    continue;
                }
                return TraRes::UnknownForAbsentPathNode;
            }

            return TraRes::UnknownForAbsentPathLinks;
        }

        if node.entry() {
            TraRes::Ok(node)
        } else {
            TraRes::UnknownForNotEntry
        }
    }

    /// `Trie` uses internal buffer, to avoid excessive allocations and copying, which grows
    /// over time due backtracing in `delete` method which backtraces whole path from entry
    /// node to root node.
    ///
    /// Use this method to shrink or extend it to fit actual program needs. Neither shrinking nor extending
    /// is guaranteed to be exact. See `Vec::with_capacity()` and `Vec::reserve()`. For optimal `delete` performance, set `approx_cap` to, at least, key length.
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
        let tr = &mut self.btr;
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
        self.btr.capacity()
    }
}

#[cfg_attr(test, derive(PartialEq, Debug))]
enum TraRes<'a, T> {
    Ok(&'a Node<T>),
    ZeroLenKey,
    UnknownForNotEntry,
    UnknownForAbsentPathLinks,
    UnknownForAbsentPathNode,
}

impl<'a, T> TraRes<'a, T> {
    fn key_err(&self) -> KeyErr {
        match self {
            TraRes::ZeroLenKey => KeyErr::ZeroLen,
            TraRes::UnknownForNotEntry
            | TraRes::UnknownForAbsentPathLinks
            | TraRes::UnknownForAbsentPathNode => KeyErr::Unknown,
            _ => panic!("Unsupported arm match."),
        }
    }
}

#[cfg_attr(test, derive(PartialEq, Clone))]
struct Node<T> {
    links: Option<Links<T>>,
    entry: Option<T>,
}

impl<T> Node<T> {
    fn entry(&self) -> bool {
        self.entry.is_some()
    }

    fn links(&self) -> bool {
        self.links.is_some()
    }

    fn empty() -> Self {
        Node {
            links: None,
            entry: None,
        }
    }
}

#[cfg(test)]
use std::fmt::{Debug, Formatter};

#[cfg(test)]
impl<T> Debug for Node<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let links = if self.links() { "Some" } else { "None" };

        f.write_fmt(format_args!(
            "Node {{\n  links: {:?}\n  entry: {:?}\n}}",
            links, self.entry
        ))
    }
}

#[cfg(test)]
mod tests_of_units {

    mod trie {
        use crate::Trie;

        #[test]
        fn new() {
            let trie = Trie::<usize>::new();

            let root = trie.root;
            assert!(!root.entry());

            let links = &root.links;
            assert!(links.is_none());
        }

        mod ins {
            use crate::{AcqRes, InsRes, KeyErr, Trie};

            #[test]
            fn zero_length_key() {
                let mut trie = Trie::new();
                let proof = InsRes::Err(KeyErr::ZeroLen);
                let test = trie.ins(0usize, "".chars());
                assert_eq!(proof, test);
            }

            #[test]
            fn basic_test() {
                const KEY: &str = "touchstone";

                let mut trie = Trie::new();
                let res = trie.ins(3usize, KEY.chars());
                assert_eq!(InsRes::Ok((&mut 3, None)), res);

                let links = &trie.root.links.as_ref();
                assert_eq!(true, links.is_some());
                let mut links = links.unwrap();

                let last_node_ix = KEY.len() - 1;
                for (ix, c) in KEY.chars().enumerate() {
                    let node = &links.get(&c);

                    assert!(node.is_some());
                    let node = node.unwrap();

                    if ix == last_node_ix {
                        assert_eq!(false, node.links());
                        assert_eq!(Some(3), node.entry);
                    } else {
                        assert_eq!(false, node.entry());
                        assert_eq!(true, node.links());
                        links = node.links.as_ref().unwrap();
                    }
                }
            }

            #[test]
            fn existing_path_insert() {
                let existing = || "touchstone".chars();
                let new = || "touch".chars();
                let mut exi_val = 3;
                let mut new_val = 4;

                let mut trie = Trie::<usize>::new();

                let res = trie.ins(exi_val, existing());
                assert_eq!(InsRes::Ok((&mut exi_val, None)), res);

                let res = trie.ins(new_val, new());
                assert_eq!(InsRes::Ok((&mut new_val, None)), res);

                assert_eq!(AcqRes::Ok(&exi_val), trie.acq(existing()));
                assert_eq!(AcqRes::Ok(&new_val), trie.acq(new()));
            }

            #[test]
            fn singular_key() {
                let mut entry = 3;

                let mut trie = Trie::new();
                let res = trie.ins(entry, "a".chars());
                assert_eq!(InsRes::Ok((&mut entry, None)), res);

                let links = trie.root.links;
                assert_eq!(true, links.is_some());
                let links = links.unwrap();
                let node = links.get(&'a');
                assert_eq!(true, node.is_some());
                assert_eq!(Some(entry), node.unwrap().entry);
            }

            #[test]
            fn double_insert() {
                let key = "appealing delicacy";
                let keyer = || key.chars();
                let mut entry_1 = 10;
                let mut entry_2 = 20;

                let mut trie = Trie::new();
                let res = trie.ins(entry_1, keyer());
                assert_eq!(InsRes::Ok((&mut entry_1, None)), res);

                let res = trie.ins(entry_2, keyer());
                assert_eq!(InsRes::Ok((&mut entry_2, Some(entry_1))), res);

                let links = &trie.root.links.as_ref();
                assert_eq!(true, links.is_some());
                let mut links = links.unwrap();

                let last_ix = key.len() - 1;
                for (ix, c) in keyer().enumerate() {
                    let node = links.get(&c);
                    assert_eq!(true, node.is_some());
                    let node = node.unwrap();

                    if ix == last_ix {
                        assert_eq!(false, node.links());
                        assert_eq!(Some(entry_2), node.entry)
                    } else {
                        assert_eq!(true, node.links());
                        links = node.links.as_ref().unwrap();
                    }
                }
            }
        }

        mod acq {

            use crate::{AcqRes, KeyErr, Trie};

            #[test]
            fn member() {
                let key = || "Keyword".chars();
                let mut trie = Trie::new();
                trie.ins(27usize, key());

                let res = trie.acq(key());
                assert_eq!(AcqRes::Ok(&27), res);
            }

            #[test]
            fn not_member() {
                let key = "Keyword";
                let mut trie = Trie::new();
                trie.ins(0usize, key.chars());

                for key in ["Key", "Opener"] {
                    let res = trie.acq(key.chars());
                    assert_eq!(AcqRes::Err(KeyErr::Unknown), res);
                }
            }

            #[test]
            fn zero_length_key() {
                let trie = Trie::<usize>::new();
                let res = trie.acq("".chars());
                assert_eq!(AcqRes::Err(KeyErr::ZeroLen), res);
            }
        }

        #[test]
        fn as_mut() {
            let trie = Trie::<usize>::new();
            let trie_ptr = &trie as *const Trie<usize>;
            let trie_mut = unsafe { trie.as_mut() };
            assert_eq!(trie_ptr as usize, trie_mut as *mut Trie::<usize> as usize);
        }

        mod delete {
            use crate::{AcqRes, KeyErr, Trie};

            #[test]
            fn known_unknown() {
                let known = || "safe-hideaway".chars();
                let unknown = || "grave-monition".chars();

                let mut trie = Trie::new();

                let known_entry = 13;
                _ = trie.ins(known_entry, known());

                assert_eq!(Result::Ok(()), trie.delete(known()));
                assert_eq!(0, trie.btr.len());
                assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(known()));

                assert_eq!(Result::Err(()), trie.delete(unknown()));
                assert_eq!(0, trie.btr.len());
            }
        }

        // node in path to entry being deleted cannot
        // be deleted if and only if participates in
        // path to another entry where path len varies 0…m
        mod delete_actual {

            use crate::{AcqRes, KeyErr, Trie};

            #[test]
            fn basic_test() {
                let key = || "abcxyz".chars();
                let entry = 60;

                let mut trie = Trie::new();
                _ = trie.ins(entry, key());
                _ = trie.track(key(), true);

                trie.delete_actual(&mut 0);
                assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(key()));
            }

            #[test]
            fn inner_entry() {
                let mut trie = Trie::new();

                let outer = || "Keyword".chars();
                trie.ins(0usize, outer());

                let inner = || "Key".chars();
                trie.ins(0usize, inner());

                let mut esc_code = 0;
                _ = trie.track(inner(), true);
                trie.delete_actual(&mut esc_code);
                assert_eq!(1, esc_code);

                assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(inner()));
                assert_eq!(true, trie.acq(outer()).is_ok());
            }

            #[test]
            fn links_removal() {
                let key = || "Keyword".chars();
                let mut trie = Trie::new();
                trie.ins(0usize, key());

                let mut esc_code = 0;
                _ = trie.track(key(), true);
                trie.delete_actual(&mut esc_code);
                assert_eq!(4, esc_code);

                assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(key()));
                assert_eq!(None, trie.root.links);
            }

            #[test]
            fn node_composing_path() {
                let dissimilar = || "Dissimilar".chars();
                let keyword = || "Keyword".chars();

                let mut trie = Trie::new();
                trie.ins(0usize, dissimilar());
                trie.ins(0usize, keyword());

                let mut esc_code = 0;
                _ = trie.track(keyword(), true);
                trie.delete_actual(&mut esc_code);
                assert_eq!(2, esc_code);

                assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(keyword()));
                assert_eq!(true, trie.acq(dissimilar()).is_ok());
            }

            #[test]
            fn entry_under_entry() {
                let above = || "keyworder".chars();
                let under = || "keyworders".chars();
                let mut trie = Trie::new();
                trie.ins(0usize, above());
                trie.ins(0usize, under());

                let mut esc_code = 0;
                _ = trie.track(under(), true);
                trie.delete_actual(&mut esc_code);
                assert_eq!(3, esc_code);

                assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(under()));
                assert_eq!(true, trie.acq(above()).is_ok());

                _ = trie.track(above(), true);
                let btr = &trie.btr;
                let last = btr[btr.len() - 1];
                assert_eq!('r', last.0);
                let node = unsafe { last.1.as_ref() }.unwrap();
                assert_eq!(false, node.links());
            }
        }

        mod track {

            use crate::{TraRes, Trie, NULL};

            #[test]
            fn tracking() {
                let mut trie = Trie::<usize>::new();

                let duos = [("k", 12), ("key", 22), ("keyword", 45)];
                for (k, e) in duos {
                    trie.ins(e, k.chars());
                }

                let keyword_duo = duos[2];
                let keyword = keyword_duo.0;

                let res = trie.track(keyword.chars(), true);
                if let TraRes::Ok(n) = res {
                    assert_eq!(Some(keyword_duo.1), n.entry);
                } else {
                    panic!("`Not TraRes::Ok(_)`, but {:?}.", res);
                }

                let trace = trie.btr;
                let proof = format!("{}{}", NULL, keyword);
                for (ix, c) in proof.chars().enumerate() {
                    let d = trace[ix];
                    assert_eq!(c, d.0);
                }

                for (k, e) in duos {
                    let (_, node) = trace[k.len()];
                    let node = unsafe { node.as_ref() }.unwrap();
                    assert_eq!(Some(e), node.entry);
                }
            }

            #[test]
            fn ok() {
                let key = || "información meteorológica".chars();
                let entry = 444;

                let mut trie = Trie::<usize>::new();
                trie.ins(entry, key());
                let res = trie.track(key(), false);

                match res {
                    TraRes::Ok(l) => assert_eq!(Some(entry), l.entry),
                    _ => panic!("`Not TraRes::Ok(_)`, but {:?}.", res),
                }
            }

            #[test]
            fn zero_length_key() {
                let mut trie = Trie::<usize>::new();
                let res = trie.track("".chars(), false);
                assert_eq!(TraRes::ZeroLenKey, res);
            }

            #[test]
            fn unknown_not_path() {
                let key = || "wordbook".chars();
                let bad_key = || "wordbooks".chars();

                let mut trie = Trie::new();
                trie.ins(500, key());
                let res = trie.track(bad_key(), false);
                assert_eq!(TraRes::UnknownForAbsentPathLinks, res);
            }

            #[test]
            fn unknown_not_path2() {
                let key = || "wordbookz".chars();
                let bad_key = || "wordbooks".chars();

                let mut trie = Trie::new();
                trie.ins(500, key());
                let res = trie.track(bad_key(), false);
                assert_eq!(TraRes::UnknownForAbsentPathNode, res);
            }

            #[test]
            fn unknown_not_entry() {
                let key = || "wordbooks".chars();
                let bad_key = || "wordbook".chars();

                let mut trie = Trie::new();
                trie.ins(777, key());

                let res = trie.track(bad_key(), false);
                assert_eq!(TraRes::UnknownForNotEntry, res);
            }
        }

        mod put_trace_cap {
            use crate::Trie;

            #[test]
            fn extend() {
                let new_cap = 10;

                let mut trie = Trie::<usize>::new();
                assert!(trie.btr.capacity() < new_cap);

                let cap = trie.put_trace_cap(new_cap);
                assert!(cap >= new_cap);
                assert!(trie.btr.capacity() >= new_cap);
            }

            #[test]
            fn shrink() {
                let new_cap = 10;
                let old_cap = 50;

                let mut trie = Trie::<usize>::new();
                trie.btr = Vec::with_capacity(old_cap);

                let cap = trie.put_trace_cap(new_cap);
                assert!(cap >= new_cap && cap < old_cap);
                let cap = trie.btr.capacity();
                assert!(cap >= new_cap && cap < old_cap);
            }

            #[test]
            fn same() {
                let approx_cap = 10;
                let mut trie = Trie::<usize>::new();
                let b_tr = &mut trie.btr;

                assert!(b_tr.capacity() < approx_cap);
                b_tr.reserve_exact(approx_cap);
                let cap = b_tr.capacity();

                let size = trie.put_trace_cap(cap);
                assert_eq!(cap, size);
                assert_eq!(cap, trie.btr.capacity());
            }
        }

        #[test]
        fn acq_trace_cap() {
            let cap = 10;
            let mut trie = Trie::<usize>::new();
            let b_tr = &mut trie.btr;

            assert!(b_tr.capacity() < cap);
            b_tr.reserve_exact(cap);
            let cap = b_tr.capacity();

            assert_eq!(cap, trie.acq_trace_cap());
        }
    }

    mod tra_res {
        use crate::{KeyErr, Node, TraRes};

        #[test]
        fn key_err_supported() {
            assert_eq!(KeyErr::ZeroLen, TraRes::<u8>::ZeroLenKey.key_err());
            assert_eq!(KeyErr::Unknown, TraRes::<u8>::UnknownForNotEntry.key_err());
            assert_eq!(
                KeyErr::Unknown,
                TraRes::<u8>::UnknownForAbsentPathLinks.key_err()
            );
            assert_eq!(
                KeyErr::Unknown,
                TraRes::<u8>::UnknownForAbsentPathNode.key_err()
            );
        }

        #[test]
        #[should_panic(expected = "Unsupported arm match.")]
        fn key_err_unsupported() {
            let mut n = Node::<usize>::empty();
            _ = TraRes::Ok(&mut n).key_err()
        }
    }

    mod node {

        use crate::{Links, Node};

        #[test]
        fn entry() {
            let mut node = Node::<usize>::empty();

            assert!(!node.entry());
            node.entry = Some(1);
            assert!(node.entry());
        }

        #[test]
        fn links() {
            let mut node = Node::<usize>::empty();

            assert!(!node.links());
            node.links = Some(Links::new());
            assert!(node.links());
        }

        #[test]
        fn empty() {
            let node = Node::<usize>::empty();

            assert!(node.links.is_none());
            assert!(node.entry.is_none());
        }
    }

    mod readme {
        use crate::{AcqRes, KeyErr, Trie};

        #[test]
        fn test() {
            let mut trie = Trie::<char>::new();

            let some = "información meteorológica".chars();
            trie.ins('🌩', some.clone());

            let one_more = "alimentación RSS".chars();
            trie.ins('😋', one_more.clone());

            assert!(trie.delete(one_more.clone()).is_ok());
            assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(one_more.clone()));
            assert_eq!(AcqRes::Ok(&'🌩'), trie.acq(some.clone()));
        }
    }
}

// cargo test --release
