//! Dynamic trie in contrast to classic trie does not have fixed size alphabet associated with node.
//!
//! Each node has dynamic alphabet of size as to satisfy exactly associated branches.

use std::collections::hash_map::HashMap;

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

    /// Inserts entry into tree.
    pub fn insert(&mut self, entry: T, mut key: impl Iterator<Item = char>) {
        let mut node = &mut self.root;
        while let Some(c) = key.next() {
            let links = node.links.get_or_insert_with(|| Links::new());
            node = links.entry(c).or_insert(Node::<T>::empty());
        }

        node.entry = Some(entry);
    }

    /// `None` for unknown key.
    ///
    /// Return value is optional view onto entry in tree.
    pub fn member(&self, key: impl Iterator<Item = char>) -> Option<&T> {
        let this = unsafe { self.as_mut() };
        let res = this.track(key, false);

        if let TraRes::Ok(en) = res {
            en.entry.as_ref()
        } else {
            None
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
        let mut node = &mut self.root;
        let tr = &mut self.btr;

        if tracing {
            tr.push((NULL, node));
        }

        while let Some(c) = key.next() {
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
    UnknownForNotEntry,
    UnknownForAbsentPathLinks,
    UnknownForAbsentPathNode,
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

        mod insert {
            use crate::Trie;

            #[test]
            fn basic_test() {
                const KEY: &str = "touchstone";

                let mut trie = Trie::new();
                trie.insert(3usize, KEY.chars());

                let last_node_ix = KEY.len() - 1;

                let mut links = trie.root.links.as_ref().unwrap();

                for (ix, c) in KEY.chars().enumerate() {
                    let node = &links.get(&c);

                    assert!(node.is_some());
                    let node = node.unwrap();

                    if ix < last_node_ix {
                        let temp = &node.links;
                        assert!(!node.entry());
                        assert!(temp.is_some());
                        links = temp.as_ref().unwrap();
                    } else {
                        assert!(!node.links());

                        let entry = node.entry;
                        assert!(entry.is_some());
                        assert_eq!(3usize, entry.unwrap());
                    }
                }
            }

            #[test]
            fn existing_path_insert() {
                let existing = || "touchstone".chars();
                let new = || "touch".chars();

                let mut trie = Trie::new();
                trie.insert(3usize, existing());
                trie.insert(4usize, new());

                assert!(trie.member(existing()).is_some());
                assert!(trie.member(new()).is_some());
            }
        }

        mod member {

            use crate::Trie;

            #[test]
            fn member() {
                let key = || "Keyword".chars();
                let mut trie = Trie::new();
                trie.insert(27usize, key());

                let member = trie.member(key());
                assert!(member.is_some());
                assert_eq!(27, *member.unwrap());
            }

            #[test]
            fn not_member() {
                let key = "Keyword";
                let mut trie = Trie::new();
                trie.insert(0usize, key.chars());

                for key in ["Key", "Opener"] {
                    let member = trie.member(key.chars());
                    assert!(member.is_none());
                }
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
            use crate::Trie;

            #[test]
            fn known_unknown() {
                let known = || "safe-hideaway".chars();
                let unknown = || "grave-monition".chars();

                let mut trie = Trie::new();

                let known_entry = 13;
                _ = trie.insert(known_entry, known());

                assert_eq!(Result::Ok(()), trie.delete(known()));
                assert_eq!(0, trie.btr.len());
                assert_eq!(None, trie.member(known()));

                assert_eq!(Result::Err(()), trie.delete(unknown()));
                assert_eq!(0, trie.btr.len());
            }
        }

        // node in path to entry being deleted cannot
        // be deleted if and only if participates in
        // path to another entry where path len varies 0…m
        mod delete_actual {

            use crate::Trie;

            #[test]
            fn basic_test() {
                let key = || "abcxyz".chars();
                let entry = 60;

                let mut trie = Trie::new();
                _ = trie.insert(entry, key());
                _ = trie.track(key(), true);

                _ = trie.delete_actual(&mut 0);
                assert_eq!(None, trie.member(key()));
            }

            #[test]
            fn inner_entry() {
                let mut trie = Trie::new();

                let outer = || "Keyword".chars();
                trie.insert(0usize, outer());

                let inner = || "Key".chars();
                trie.insert(0usize, inner());

                let mut esc_code = 0;
                _ = trie.track(inner(), true);
                _ = trie.delete_actual(&mut esc_code);
                assert_eq!(1, esc_code);

                assert_eq!(None, trie.member(inner()));
                assert!(trie.member(outer()).is_some());
            }

            #[test]
            fn links_removal() {
                let key = || "Keyword".chars();
                let mut trie = Trie::new();
                trie.insert(0usize, key());

                let mut esc_code = 0;
                _ = trie.track(key(), true);
                _ = trie.delete_actual(&mut esc_code);
                assert_eq!(4, esc_code);

                assert_eq!(None, trie.member(key()));
                assert_eq!(None, trie.root.links);
            }

            #[test]
            fn node_composing_path() {
                let dissimilar = || "Dissimilar".chars();
                let keyword = || "Keyword".chars();

                let mut trie = Trie::new();
                trie.insert(0usize, dissimilar());
                trie.insert(0usize, keyword());

                let mut esc_code = 0;
                _ = trie.track(keyword(), true);
                _ = trie.delete_actual(&mut esc_code);
                assert_eq!(2, esc_code);

                assert_eq!(None, trie.member(keyword()));
                assert!(trie.member(dissimilar()).is_some());
            }

            #[test]
            fn entry_under_entry() {
                let above = || "keyworder".chars();
                let under = || "keyworders".chars();
                let mut trie = Trie::new();
                trie.insert(0usize, above());
                trie.insert(0usize, under());

                let mut esc_code = 0;
                _ = trie.track(under(), true);
                _ = trie.delete_actual(&mut esc_code);
                assert_eq!(3, esc_code);

                assert_eq!(None, trie.member(under()));
                assert!(trie.member(above()).is_some());

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
                    trie.insert(e, k.chars());
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
                trie.insert(entry, key());
                let res = trie.track(key(), false);

                match res {
                    TraRes::Ok(l) => assert_eq!(Some(entry), l.entry),
                    _ => panic!("`Not TraRes::Ok(_)`, but {:?}.", res),
                }
            }

            #[test]
            fn unknown_not_path() {
                let key = || "wordbook".chars();
                let bad_key = || "wordbooks".chars();

                let mut trie = Trie::new();
                trie.insert(500, key());
                let res = trie.track(bad_key(), false);
                assert_eq!(TraRes::UnknownForAbsentPathLinks, res);
            }

            #[test]
            fn unknown_not_path2() {
                let key = || "wordbookz".chars();
                let bad_key = || "wordbooks".chars();

                let mut trie = Trie::new();
                trie.insert(500, key());
                let res = trie.track(bad_key(), false);
                assert_eq!(TraRes::UnknownForAbsentPathNode, res);
            }

            #[test]
            fn unknown_not_entry() {
                let key = || "wordbooks".chars();
                let bad_key = || "wordbook".chars();

                let mut trie = Trie::new();
                trie.insert(777, key());

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
        use crate::Trie;

        #[test]
        fn test() {
            let mut trie = Trie::<char>::new();

            let some = "información meteorológica".chars();
            trie.insert('🌩', some.clone());

            let one_more = "alimentación RSS".chars();
            trie.insert('😋', one_more.clone());

            assert!(trie.delete(one_more.clone()).is_ok());
            assert!(trie.member(one_more.clone()).is_none());
            assert_eq!(Some(&'🌩'), trie.member(some.clone()));
        }
    }
}

// cargo test --release
