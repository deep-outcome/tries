//! Dynamic trie in contrast to classic trie does not have fixed size alphabet associated with node.
//!
//! Each node has dynamic alphabet of size as to satisfy exactly associated branches.

use core::panic;
use std::collections::hash_map::HashMap;

mod res;
use res::{tsdv, TraStrain};
pub use res::{AcqMutRes, AcqRes, InsRes, KeyErr, RemRes};

type Links<T> = HashMap<char, Node<T>>;

fn ext<T>(l: &mut Links<T>, buff: &mut String, o: &mut Vec<(String, T)>) {
    let mut l_keys = Vec::with_capacity(8);
    for lk in l.keys() {
        l_keys.push(*lk)
    }
    l_keys.sort();

    let lk_len = l_keys.len();
    let mut lk_ix = 0;
    while lk_ix < lk_len {
        let lk = l_keys[lk_ix];
        lk_ix += 1;

        buff.push(lk);

        let n = unsafe { l.get_mut(&lk).unwrap_unchecked() };

        if let Some(e) = n.entry.take() {
            let key = buff.clone();
            o.push((key, e));
        }

        if let Some(l) = n.links.as_mut() {
            ext(l, buff, o);
        }

        _ = buff.pop();
    }
}

fn view<'a, T>(l: &'a Links<T>, buff: &mut String, o: &mut Vec<(String, &'a T)>) {
    let mut l_keys = Vec::with_capacity(8);
    for lk in l.keys() {
        l_keys.push(*lk)
    }
    l_keys.sort();

    let lk_len = l_keys.len();
    let mut lk_ix = 0;
    while lk_ix < lk_len {
        let lk = l_keys[lk_ix];
        lk_ix += 1;

        buff.push(lk);

        let n = unsafe { l.get(&lk).unwrap_unchecked() };

        if let Some(e) = n.entry.as_ref() {
            let key = buff.clone();
            o.push((key, e));
        }

        if let Some(l) = n.links.as_ref() {
            view(l, buff, o);
        }

        _ = buff.pop();
    }
}

/// Retrieval tree implementation allowing for mapping any `T` to any `impl Iterator<Item = char>` type.
///
/// Node occurs per every `char` as defined by Rust lang and uses `std::collections::HashMap`
/// to linking subnodes. Thus all methods complexity is respective to hashmap methods complexity.
pub struct Trie<T> {
    root: Node<T>,
    // backtrace buff
    btr: Vec<(char, *mut Node<T>)>,
    // entries count
    cnt: usize,
}

const NULL: char = '\0';
impl<T> Trie<T> {
    /// Ctor.
    pub fn new() -> Trie<T> {
        Trie {
            root: Node::<T>::empty(),
            btr: Vec::new(),
            cnt: 0,
        }
    }

    /// Inserts entry into tree under key specified.
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

        if prev.is_none() {
            self.cnt += 1;
        }

        let curr = en.as_mut().unwrap();
        InsRes::Ok((curr, prev))
    }

    /// Acquires reference to entry associted to `key`.
    pub fn acq(&self, key: impl Iterator<Item = char>) -> AcqRes<T> {
        let this = unsafe { self.as_mut() };
        let res = this.track(key, TraStrain::NonRef);

        if let TraRes::OkRef(en) = res {
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

    /// Acquires mutable reference to entry associted to `key`.
    pub fn acq_mut(&mut self, key: impl Iterator<Item = char>) -> AcqMutRes<T> {
        match self.track(key, TraStrain::NonMut) {
            TraRes::OkMut(n) => {
                let en = n.entry.as_mut();
                AcqMutRes::Ok(unsafe { en.unwrap_unchecked() })
            }
            res => AcqMutRes::Err(res.key_err()),
        }
    }

    /// Removes key-entry duo from tree.
    ///
    /// Check with `put_trace_cap` also.
    pub fn rem(&mut self, key: impl Iterator<Item = char>) -> RemRes<T> {
        let tra_res = self.track(key, TraStrain::TraEmp);
        let res = if let TraRes::Ok = tra_res {
            let en = self.rem_actual(
                #[cfg(test)]
                &mut 0,
            );

            self.cnt -= 1;
            RemRes::Ok(en)
        } else {
            RemRes::Err(tra_res.key_err())
        };

        self.btr.clear();
        res
    }

    fn rem_actual(&mut self, #[cfg(test)] esc_code: &mut usize) -> T {
        let mut trace = self.btr.iter();
        let en_duo = trace.next_back().unwrap();
        let mut node = unsafe { en_duo.1.as_mut() }.unwrap();

        let entry = node.entry.take().unwrap();
        if node.links() {
            #[cfg(test)]
            {
                *esc_code = 1;
            }

            return entry;
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

                return entry;
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

        entry
    }

    // - c is count of `char`s iterated over
    // - TC: Ω(c ⋅1~) when `tracing = true`, ϴ(c ⋅1~) otherwise
    // - SC: ϴ(c ⋅1~) when `tracing = true`, ϴ(0 ⋅1~) otherwise
    fn track<'a>(
        &'a mut self,
        mut key: impl Iterator<Item = char>,
        ts: TraStrain,
    ) -> TraRes<'a, T> {
        let mut next = key.next();

        if next.is_none() {
            return TraRes::ZeroLenKey;
        }

        let mut node = &mut self.root;
        let tr = &mut self.btr;

        let tracing = TraStrain::has(ts.clone(), tsdv::TRA);
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
            match ts {
                x if TraStrain::has(x.clone(), tsdv::REF) => TraRes::OkRef(node),
                x if TraStrain::has(x.clone(), tsdv::MUT) => TraRes::OkMut(node),
                x if TraStrain::has(x.clone(), tsdv::EMP) => TraRes::Ok,
                _ => panic!("Unsupported result scenario."),
            }
        } else {
            TraRes::UnknownForNotEntry
        }
    }

    /// `Trie` uses internal buffer, to avoid excessive allocations and copying, which grows
    /// over time due backtracing in `rem` method which backtraces whole path from entry
    /// node to root node.
    ///
    /// Use this method to shrink or extend it to fit actual program needs. Neither shrinking nor extending
    /// is guaranteed to be exact. See `Vec::with_capacity()` and `Vec::reserve()`. For optimal `rem` performance, set `approx_cap` to, at least, key length.
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

    /// Clears tree.
    ///
    /// Does not reset backtracing buffer. Check with `fn put_trace_cap` for details.
    pub fn clr(&mut self) {
        self.root = Node::<T>::empty();
        self.cnt = 0;
    }

    /// Return value is count of entries in tree.
    pub const fn ct(&self) -> usize {
        self.cnt
    }

    /// Extracts key-entry duos from tree. Leaves tree empty.
    ///
    /// Extraction is alphabetically ordered.    
    pub fn ext(&mut self) -> Vec<(String, T)> {
        // capacity is prebuffered to 1000
        let mut buff = String::with_capacity(1000);

        // capacity is prebuffered to 1000
        let mut res = Vec::with_capacity(1000);

        if let Some(rl) = &mut self.root.links {
            ext(rl, &mut buff, &mut res);
        }

        res.shrink_to_fit();
        self.clr();
        res
    }

    /// Creates view onto key-entry duos in tree.
    ///
    /// View is alphabetically ordered.
    pub fn view(&self) -> Vec<(String, &T)> {
        // capacity is prebuffered to 1000
        let mut buff = String::with_capacity(1000);

        // capacity is prebuffered to 1000
        let mut res = Vec::with_capacity(1000);

        if let Some(rl) = &self.root.links {
            view(rl, &mut buff, &mut res);
        }

        res.shrink_to_fit();
        res
    }
}

#[cfg_attr(test, derive(PartialEq, Debug))]
enum TraRes<'a, T> {
    Ok,
    OkRef(&'a Node<T>),
    OkMut(&'a mut Node<T>),
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

    mod ext {

        use crate::{ext, AcqRes, KeyErr, Trie};

        #[test]
        fn basic_test() {
            let mut trie = Trie::new();

            let a = || "a".chars();
            let z = || "z".chars();

            _ = trie.ins(1usize, a());
            _ = trie.ins(2usize, z());

            let mut buff = String::new();
            let mut test = Vec::new();

            let links = unsafe { trie.root.links.as_mut().unwrap_unchecked() };
            ext(links, &mut buff, &mut test);

            let proof = vec![(String::from("a"), 1), (String::from("z"), 2)];
            assert_eq!(proof, test);

            assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(a()));
            assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(z()));
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
                _ = trie.ins(e.1, e.0.chars());
            }

            let mut buff = String::new();
            let mut test = Vec::new();

            let links = unsafe { trie.root.links.as_mut().unwrap_unchecked() };
            ext(links, &mut buff, &mut test);

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
                _ = trie.ins(p.1, p.0.chars());
            }

            let mut buff = String::new();
            let mut test = Vec::new();

            let links = unsafe { trie.root.links.as_mut().unwrap_unchecked() };
            ext(links, &mut buff, &mut test);

            assert_eq!(paths, test);
        }
    }

    mod view {

        use crate::{view, Trie};

        #[test]
        fn basic_test() {
            let mut trie = Trie::new();

            let a = || "a".chars();
            let z = || "z".chars();

            let a_entry = 1usize;
            let z_entry = 2;

            _ = trie.ins(a_entry, a());
            _ = trie.ins(z_entry, z());

            let mut buff = String::new();
            let mut test = Vec::new();

            let links = unsafe { trie.root.links.as_ref().unwrap_unchecked() };
            view(links, &mut buff, &mut test);

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
                _ = trie.ins(*e.1, e.0.chars());
            }

            let mut buff = String::new();
            let mut test = Vec::new();

            let links = unsafe { trie.root.links.as_ref().unwrap_unchecked() };
            view(links, &mut buff, &mut test);

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
                _ = trie.ins(*p.1, p.0.chars());
            }

            let mut buff = String::new();
            let mut test = Vec::new();

            let links = unsafe { trie.root.links.as_ref().unwrap_unchecked() };
            view(links, &mut buff, &mut test);

            assert_eq!(paths, test);
        }
    }

    mod trie {
        use crate::Trie;

        #[test]
        fn new() {
            let trie = Trie::<usize>::new();

            let root = trie.root;
            assert!(!root.entry());

            let links = &root.links;
            assert!(links.is_none());

            assert_eq!(0, trie.cnt);
        }

        mod ins {
            use crate::{AcqRes, InsRes, KeyErr, Trie};

            #[test]
            fn zero_length_key() {
                let mut trie = Trie::new();
                let proof = InsRes::Err(KeyErr::ZeroLen);
                let test = trie.ins(0usize, "".chars());
                assert_eq!(proof, test);
                assert_eq!(0, trie.cnt);
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

                assert_eq!(1, trie.cnt);
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
                assert_eq!(1, trie.cnt);

                let res = trie.ins(new_val, new());
                assert_eq!(InsRes::Ok((&mut new_val, None)), res);
                assert_eq!(2, trie.cnt);

                assert_eq!(AcqRes::Ok(&exi_val), trie.acq(existing()));
                assert_eq!(AcqRes::Ok(&new_val), trie.acq(new()));
            }

            #[test]
            fn singular_key() {
                let mut entry = 3;

                let mut trie = Trie::new();
                let res = trie.ins(entry, "a".chars());
                assert_eq!(InsRes::Ok((&mut entry, None)), res);
                assert_eq!(1, trie.cnt);

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
                assert_eq!(1, trie.cnt);

                let res = trie.ins(entry_2, keyer());
                assert_eq!(InsRes::Ok((&mut entry_2, Some(entry_1))), res);
                assert_eq!(1, trie.cnt);

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

        mod acq_mut {

            use crate::{AcqMutRes, KeyErr, Trie};

            #[test]
            fn member() {
                let key = || "Keyword".chars();
                let mut trie = Trie::new();
                trie.ins(27usize, key());

                let res = trie.acq_mut(key());
                assert_eq!(AcqMutRes::Ok(&mut 27), res);
            }

            #[test]
            fn not_member() {
                let key = "Keyword";
                let mut trie = Trie::new();
                trie.ins(0usize, key.chars());

                for key in ["Key", "Opener"] {
                    let res = trie.acq_mut(key.chars());
                    assert_eq!(AcqMutRes::Err(KeyErr::Unknown), res);
                }
            }

            #[test]
            fn zero_length_key() {
                let mut trie = Trie::<usize>::new();
                let res = trie.acq_mut("".chars());
                assert_eq!(AcqMutRes::Err(KeyErr::ZeroLen), res);
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
                let known = || "safe-hideaway".chars();
                let unknown = || "grave-monition".chars();

                let mut trie = Trie::new();

                let known_entry = 13;
                _ = trie.ins(known_entry, known());

                assert_eq!(RemRes::Err(KeyErr::Unknown), trie.rem(unknown()));
                assert_eq!(0, trie.btr.len());
                assert_eq!(1, trie.cnt);

                assert_eq!(RemRes::Ok(known_entry), trie.rem(known()));
                assert_eq!(0, trie.btr.len());
                assert_eq!(0, trie.cnt);
                assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(known()));
            }

            #[test]
            fn zero_length_key() {
                let mut trie = Trie::<usize>::new();
                let res = trie.rem("".chars());
                assert_eq!(RemRes::Err(KeyErr::ZeroLen), res);
            }
        }

        // node in path to entry being deleted cannot
        // be deleted if and only if participates in
        // path to another entry where path len varies 0…m
        mod rem_actual {

            use crate::{AcqRes, KeyErr, TraStrain, Trie};

            #[test]
            fn basic_test() {
                let key = || "abcxyz".chars();
                let entry = 60;

                let mut trie = Trie::new();
                _ = trie.ins(entry, key());
                _ = trie.track(key(), TraStrain::TraEmp);

                assert_eq!(entry, trie.rem_actual(&mut 0));
                assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(key()));
            }

            #[test]
            fn inner_entry() {
                let mut trie = Trie::new();

                let outer = || "Keyword".chars();
                trie.ins(0usize, outer());

                let inner = || "Key".chars();
                trie.ins(1usize, inner());

                let mut esc_code = 0;
                _ = trie.track(inner(), TraStrain::TraEmp);

                assert_eq!(1, trie.rem_actual(&mut esc_code));
                assert_eq!(1, esc_code);

                assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(inner()));
                assert_eq!(true, trie.acq(outer()).is_ok());
            }

            #[test]
            fn links_removal() {
                let key = || "Keyword".chars();
                let mut trie = Trie::new();
                trie.ins(1usize, key());

                let mut esc_code = 0;
                _ = trie.track(key(), TraStrain::TraEmp);
                assert_eq!(1, trie.rem_actual(&mut esc_code));
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
                trie.ins(1usize, keyword());

                let mut esc_code = 0;
                _ = trie.track(keyword(), TraStrain::TraEmp);
                assert_eq!(1, trie.rem_actual(&mut esc_code));
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
                trie.ins(1usize, under());

                let mut esc_code = 0;
                _ = trie.track(under(), TraStrain::TraEmp);
                assert_eq!(1, trie.rem_actual(&mut esc_code));
                assert_eq!(3, esc_code);

                assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(under()));
                assert_eq!(true, trie.acq(above()).is_ok());

                _ = trie.track(above(), TraStrain::TraEmp);
                let btr = &trie.btr;
                let last = btr[btr.len() - 1];
                assert_eq!('r', last.0);
                let node = unsafe { last.1.as_ref() }.unwrap();
                assert_eq!(false, node.links());
            }
        }

        mod track {

            use crate::{TraRes, TraStrain, Trie, NULL};

            #[test]
            fn tracking() {
                let mut trie = Trie::<usize>::new();

                let duos = [("k", 12), ("key", 22), ("keyword", 45)];
                for (k, e) in duos {
                    trie.ins(e, k.chars());
                }

                let keyword_duo = duos[2];
                let keyword = keyword_duo.0;

                _ = trie.track(keyword.chars(), TraStrain::TraEmp);

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

                let mut trie = Trie::<usize>::new();
                _ = trie.ins(0, key());
                let res = trie.track(key(), TraStrain::NonEmp);

                match res {
                    TraRes::Ok => {}
                    _ => panic!("`Not TraRes::Ok`, but {:?}.", res),
                }
            }

            #[test]
            fn ok_ref() {
                let key = || "información meteorológica".chars();
                let entry = 444;

                let mut trie = Trie::<usize>::new();
                _ = trie.ins(entry, key());
                let res = trie.track(key(), TraStrain::NonRef);

                match res {
                    TraRes::OkRef(n) => assert_eq!(Some(entry), n.entry),
                    _ => panic!("`Not TraRes::OkRef(_)`, but {:?}.", res),
                }
            }

            #[test]
            fn ok_mut() {
                let key = || "información meteorológica".chars();
                let entry = 444;

                let mut trie = Trie::<usize>::new();
                _ = trie.ins(entry, key());
                let res = trie.track(key(), TraStrain::NonMut);

                match res {
                    TraRes::OkMut(n) => assert_eq!(Some(entry), n.entry),
                    _ => panic!("`Not TraRes::OkMut(_)`, but {:?}.", res),
                }
            }

            #[test]
            #[should_panic(expected = "Unsupported result scenario.")]
            fn unsupported_result() {
                let key = || "información meteorológica".chars();

                let mut trie = Trie::<usize>::new();
                _ = trie.ins(0, key());

                _ = trie.track(key(), TraStrain::Unset);
            }

            #[test]
            fn zero_length_key() {
                let mut trie = Trie::<usize>::new();
                let res = trie.track("".chars(), TraStrain::NonEmp);
                assert_eq!(TraRes::ZeroLenKey, res);
            }

            #[test]
            fn unknown_not_path() {
                let key = || "wordbook".chars();
                let bad_key = || "wordbooks".chars();

                let mut trie = Trie::new();
                _ = trie.ins(500, key());
                let res = trie.track(bad_key(), TraStrain::NonEmp);
                assert_eq!(TraRes::UnknownForAbsentPathLinks, res);
            }

            #[test]
            fn unknown_not_path2() {
                let key = || "wordbookz".chars();
                let bad_key = || "wordbooks".chars();

                let mut trie = Trie::new();
                _ = trie.ins(500, key());
                let res = trie.track(bad_key(), TraStrain::NonEmp);
                assert_eq!(TraRes::UnknownForAbsentPathNode, res);
            }

            #[test]
            fn unknown_not_entry() {
                let key = || "wordbooks".chars();
                let bad_key = || "wordbook".chars();

                let mut trie = Trie::new();
                _ = trie.ins(777, key());

                let res = trie.track(bad_key(), TraStrain::NonEmp);
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

        use crate::{AcqRes, KeyErr, Node};

        #[test]
        fn clr() {
            let key = "Key".chars();
            let mut trie = Trie::new();

            _ = trie.ins(77usize, key.clone());

            let mut cap = 50;
            assert!(trie.acq_trace_cap() < cap);
            cap = trie.put_trace_cap(cap);

            trie.clr();
            assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(key));
            assert_eq!(Node::empty(), trie.root);
            assert_eq!(0, trie.cnt);

            assert_eq!(cap, trie.acq_trace_cap());
        }

        #[test]
        fn ct() {
            let test = 3;
            let mut trie = Trie::<usize>::new();
            assert_eq!(0, trie.ct());
            trie.cnt = test;
            assert_eq!(test, trie.ct());
        }

        mod ext {
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
                    _ = trie.ins(t.1, t.0.chars());
                }

                let ext = trie.ext();
                assert_eq!(test, ext);
                assert!(ext.capacity() < 1000);

                for t in test.iter() {
                    assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(t.0.chars()));
                }
            }

            #[test]
            fn empty_tree() {
                let mut trie = Trie::<usize>::new();
                let ext = trie.ext();

                assert_eq!(0, ext.len());
                assert!(ext.capacity() < 1000);
            }
        }

        mod view {

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
                    _ = trie.ins(*t.1, t.0.chars());
                }

                let view = trie.view();
                assert_eq!(test, view);
                assert!(view.capacity() < 1000);

                for t in test.iter() {
                    assert_eq!(AcqRes::Ok(t.1), trie.acq(t.0.chars()));
                }
            }

            #[test]
            fn empty_tree() {
                let trie = Trie::<usize>::new();
                let view = trie.view();

                assert_eq!(0, view.len());
                assert!(view.capacity() < 1000);
            }
        }
    }

    mod tra_res {
        use crate::{KeyErr, TraRes};

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
            _ = TraRes::<usize>::Ok.key_err()
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
        use crate::{AcqRes, KeyErr, RemRes, Trie};

        #[test]
        fn test() {
            let mut trie = Trie::<char>::new();

            let some = "información meteorológica".chars();
            trie.ins('🌩', some.clone());

            let one_more = "alimentación RSS".chars();
            trie.ins('😋', one_more.clone());

            assert_eq!(RemRes::Ok('😋'), trie.rem(one_more.clone()));
            assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(one_more.clone()));
            assert_eq!(AcqRes::Ok(&'🌩'), trie.acq(some.clone()));
        }
    }
}

// cargo test --release
