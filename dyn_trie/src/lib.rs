//! Dynamic trie in contrast to classic trie does not have fixed size alphabet associated with node.
//!
//! Each node has dynamic alphabet of size as to satisfy associated branches.

use core::panic;
use std::collections::hash_map::HashMap;

mod res;
pub use res::{InsRes, InsResAide, KeyErr};

mod tra;
use tra::{tsdv, TraStrain};

mod uc;
use uc::UC;

/// Tree node branches.
///
/// [`char`] is mapped to [`Node`].
pub type Branches<T> = HashMap<char, Node<T>>;

fn ext<T>(b: &mut Branches<T>, buff: &mut String, o: &mut Vec<(String, T)>) {
    for (k, n) in b.iter_mut() {
        buff.push(*k);

        if let Some(e) = n.entry.take() {
            let key = buff.clone();
            o.push((key, e));
        }

        if let Some(b) = n.branches.as_mut() {
            ext(b, buff, o);
        }

        _ = buff.pop();
    }
}

fn view<'a, T>(b: &'a Branches<T>, buff: &mut String, o: &mut Vec<(String, &'a T)>) {
    for (k, n) in b.iter() {
        buff.push(*k);

        if let Some(e) = n.entry.as_ref() {
            let key = buff.clone();
            o.push((key, e));
        }

        if let Some(b) = n.branches.as_ref() {
            view(b, buff, o);
        }

        _ = buff.pop();
    }
}

/// Retrieval tree implementation allowing for mapping any `T` to any `impl Iterator<Item = char>` type.
///
/// Node occurs per every [`char`] as defined by Rust lang and uses [`std::collections::HashMap`]
/// to linking subnodes. Thus all methods complexity is respective to hashmap methods complexity.
pub struct Trie<T> {
    root: Node<T>,
    // backtrace buff
    btr: UC<Vec<(char, *mut Node<T>)>>,
    // entries count
    cnt: usize,
}

const NULL: char = '\0';
impl<T> Trie<T> {
    /// Ctor.
    pub const fn new() -> Trie<T> {
        Trie {
            root: Node::<T>::empty(),
            btr: UC::new(Vec::new()),
            cnt: 0,
        }
    }

    /// Inserts entry into tree under key specified.
    ///
    /// Only invalid key recognized is zero-length key.
    ///
    /// ```
    /// use dyn_trie::{Trie, InsResAide};
    ///
    /// let mut trie = Trie::new();
    /// let mut key = || "abc".chars();
    ///
    /// let test = trie.ins(3, key());
    /// assert!(test.is_ok());
    ///
    /// let test = trie.ins(4, key());
    /// assert_eq!(3, test.unwrap().uproot_previous());
    /// ```
    pub fn ins(
        &mut self,
        entry: T,
        mut key: impl Iterator<Item = char>,
    ) -> Result<InsRes<'_, T>, KeyErr> {
        let mut next = key.next();

        if next.is_none() {
            return Err(KeyErr::ZeroLen);
        }

        let mut node = &mut self.root;
        while let Some(c) = next {
            let branches = node.branches.get_or_insert_with(|| Branches::new());
            node = branches.entry(c).or_insert(Node::<T>::empty());

            next = key.next();
        }

        let en = &mut node.entry;
        let prev = en.replace(entry);

        if prev.is_none() {
            self.cnt += 1;
        }

        let curr = en.as_mut().unwrap();
        Ok((curr, prev))
    }

    /// Acquires reference to entry associted to `key`.
    pub fn acq(&self, key: impl Iterator<Item = char>) -> Result<&T, KeyErr> {
        let res = self.track(key, TraStrain::NonRef);

        if let TraRes::OkRef(en) = res {
            let en = en.entry.as_ref();
            Ok(unsafe { en.unwrap_unchecked() })
        } else {
            Err(res.key_err())
        }
    }

    /// Acquires mutable reference to entry associted to `key`.
    pub fn acq_mut(&mut self, key: impl Iterator<Item = char>) -> Result<&mut T, KeyErr> {
        match self.track(key, TraStrain::NonMut) {
            TraRes::OkMut(n) => {
                let en = n.entry.as_mut();
                Ok(unsafe { en.unwrap_unchecked() })
            }
            res => Err(res.key_err()),
        }
    }

    /// Removes key-entry duo from tree.
    ///
    /// Check with [`Trie::put_trace_cap`] also.
    pub fn rem(&mut self, key: impl Iterator<Item = char>) -> Result<T, KeyErr> {
        let tra_res = self.track(key, TraStrain::TraEmp);
        let res = if let TraRes::Ok = tra_res {
            let en = self.rem_actual(
                #[cfg(test)]
                &mut 0,
            );

            self.cnt -= 1;
            Ok(en)
        } else {
            Err(tra_res.key_err())
        };

        self.btr.get_mut().clear();
        res
    }

    fn rem_actual(&self, #[cfg(test)] esc_code: &mut usize) -> T {
        let mut trace = self.btr.iter();
        let en_duo = unsafe { trace.next_back().unwrap_unchecked() };
        let mut node = unsafe { en_duo.1.as_mut().unwrap_unchecked() };

        let entry = node.entry.take().unwrap();
        if node.branches() {
            #[cfg(test)]
            set_code(1, esc_code);

            return entry;
        }

        // subnode key
        let mut sn_key = &en_duo.0;
        while let Some((c, n)) = trace.next_back() {
            node = unsafe { n.as_mut().unwrap_unchecked() };
            let branches = unsafe { node.branches.as_mut().unwrap_unchecked() };
            _ = branches.remove(sn_key);

            #[cfg(test)]
            set_code(2, esc_code);

            if branches.len() > 0 {
                #[cfg(test)]
                set_code(4, esc_code);

                return entry;
            }

            if node.entry() {
                #[cfg(test)]
                set_code(8, esc_code);

                break;
            }

            sn_key = c;
        }

        node.branches = None;
        #[cfg(test)]
        if *esc_code != (2 | 8) {
            set_code(16, esc_code);
        }

        return entry;

        #[cfg(test)]
        fn set_code(c: usize, esc_code: &mut usize) {
            let code = *esc_code;
            *esc_code = code | c;
        }
    }

    // - c is count of `char`s iterated over
    // - TC: Ω(c ⋅1~) when `tracing = true`, ϴ(c ⋅1~) otherwise
    // - SC: ϴ(c ⋅1~) when `tracing = true`, ϴ(0 ⋅1~) otherwise
    fn track<'a>(&'a self, mut key: impl Iterator<Item = char>, ts: TraStrain) -> TraRes<'a, T> {
        let mut next = key.next();

        if next.is_none() {
            return TraRes::ZeroLenKey;
        }

        let mut node = &self.root;
        let tr = self.btr.get_mut();

        let tracing = TraStrain::has(ts.clone(), tsdv::TRA);
        if tracing {
            tr.push((NULL, node.to_mut_ptr()));
        }

        while let Some(c) = next {
            next = key.next();

            if let Some(b) = node.branches.as_ref() {
                if let Some(n) = b.get(&c) {
                    if tracing {
                        tr.push((c, n.to_mut_ptr()));
                    }

                    node = n;
                    continue;
                }
                return TraRes::UnknownForAbsentPathNode;
            }

            return TraRes::UnknownForAbsentPathBranches;
        }

        if node.entry() {
            match ts {
                x if TraStrain::has(x.clone(), tsdv::REF) => TraRes::OkRef(node),
                x if TraStrain::has(x.clone(), tsdv::MUT) => {
                    let n_mut = unsafe { node.to_mut_ptr().as_mut().unwrap_unchecked() };
                    TraRes::OkMut(n_mut)
                }
                x if TraStrain::has(x.clone(), tsdv::EMP) => TraRes::Ok,
                _ => panic!("Unsupported result scenario."),
            }
        } else {
            TraRes::UnknownForNotEntry
        }
    }

    /// [`Trie`] uses internal buffer, to avoid excessive allocations and copying, which grows
    /// over time due backtracing in [`Trie::rem`] method which backtraces whole path from entry
    /// node to root node.
    ///
    /// Use this method to shrink or extend it to fit actual program needs. Neither shrinking nor extending
    /// is guaranteed to be exact. See [`Vec::with_capacity()`] and [`Vec::reserve()`]. For optimal [`Trie::rem`] performance, set `approx_cap` to, at least, key length.
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
        let tr = &mut self.btr;
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
        self.btr.capacity()
    }

    /// Clears tree.
    ///
    /// Return value is count of entries before clearing.
    ///
    /// Does not reset backtracing buffer. Check with [`Trie::put_trace_cap`] for details.
    pub fn clr(&mut self) -> usize {
        self.root = Node::<T>::empty();

        let cnt = self.cnt;
        self.cnt = 0;
        cnt
    }

    /// Return value is count of entries in tree.
    pub const fn ct(&self) -> usize {
        self.cnt
    }

    /// Extracts key-entry duos from tree. Leaves tree empty.
    ///
    /// Extraction is alphabetically unordered. Exactly, order depends on
    /// order given by [`std::collections::hash_map::IterMut`] iterator produced by
    /// [`std::collections::HashMap::iter_mut`] at each node.
    ///
    /// Return value is [`None`] for empty [`Trie`].
    ///
    /// Returned set can be overcapacitated, i.e. its capacity
    /// will not be shrunken according to its length.
    pub fn ext(&mut self) -> Option<Vec<(String, T)>> {
        if self.cnt == 0 {
            return None;
        }

        // capacity is prebuffered to 1000
        let mut buff = String::with_capacity(1000);

        // capacity is prebuffered to 1000
        let mut res = Vec::with_capacity(1000);

        let rl = unsafe { self.root.branches.as_mut().unwrap_unchecked() };
        ext(rl, &mut buff, &mut res);

        _ = self.clr();
        Some(res)
    }

    /// Creates view onto key-entry duos in tree.
    ///
    /// View is alphabetically unordered. Exactly, order depends on
    /// order given by [`std::collections::hash_map::Iter`] iterator produced by
    /// [`std::collections::HashMap::iter`] at each node.
    ///
    /// Return value is [`None`] for empty [`Trie`].
    ///
    /// Returned set can be overcapacitated, i.e. its capacity
    /// will not be shrunken according to its length.
    pub fn view(&self) -> Option<Vec<(String, &T)>> {
        if self.cnt == 0 {
            return None;
        }

        // capacity is prebuffered to 1000
        let mut buff = String::with_capacity(1000);

        // capacity is prebuffered to 1000
        let mut res = Vec::with_capacity(1000);

        let rl = unsafe { self.root.branches.as_ref().unwrap_unchecked() };
        view(rl, &mut buff, &mut res);

        Some(res)
    }

    /// For non-empty tree, provides reference access to tree root branches. [`None`] otherwise.
    ///
    /// Intended for functional extension of trie.
    pub fn as_ref(&self) -> Option<&Branches<T>> {
        self.root.branches.as_ref()
    }

    /// For non-empty tree, provides mutable reference access to tree root branches. [`None`] otherwise.
    ///
    /// Intended for functional extension of trie.
    pub fn as_mut(&mut self) -> Option<&mut Branches<T>> {
        self.root.branches.as_mut()
    }
}

#[cfg_attr(test, derive(PartialEq, Debug))]
enum TraRes<'a, T> {
    Ok,
    OkRef(&'a Node<T>),
    OkMut(&'a mut Node<T>),
    ZeroLenKey,
    UnknownForNotEntry,
    UnknownForAbsentPathBranches,
    UnknownForAbsentPathNode,
}

impl<'a, T> TraRes<'a, T> {
    const fn key_err(&self) -> KeyErr {
        match self {
            TraRes::ZeroLenKey => KeyErr::ZeroLen,
            TraRes::UnknownForNotEntry
            | TraRes::UnknownForAbsentPathBranches
            | TraRes::UnknownForAbsentPathNode => KeyErr::Unknown,
            _ => panic!("Unsupported arm match."),
        }
    }
}

/// Tree node.
///
/// It is associated with `char` in [`Branches`].
/// Optionally: can link to entries and hold some entry.
#[derive(PartialEq, Clone)]
pub struct Node<T> {
    /// Node branches to sub-level nodes.
    pub branches: Option<Branches<T>>,
    /// Entry if node is entry node. [`None`] otherwise.
    pub entry: Option<T>,
}

impl<T> Node<T> {
    const fn entry(&self) -> bool {
        self.entry.is_some()
    }

    const fn branches(&self) -> bool {
        self.branches.is_some()
    }

    const fn empty() -> Self {
        Node {
            branches: None,
            entry: None,
        }
    }

    const fn to_mut_ptr(&self) -> *mut Self {
        (self as *const Self).cast_mut()
    }
}

use std::fmt::{Debug, Formatter};

impl<T> Debug for Node<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let branches = if self.branches() { "Some" } else { "None" };

        f.write_fmt(format_args!(
            "Node {{\n  branches: {}\n  entry: {:?}\n}}",
            branches, self.entry
        ))
    }
}

#[cfg(test)]
mod aide;

#[cfg(test)]
mod tests_of_units {

    mod ext {

        use crate::{ext, KeyErr, Trie};

        #[test]
        fn basic_test() {
            let mut trie = Trie::new();

            let a = || "a".chars();
            let z = || "z".chars();

            _ = trie.ins(1usize, a());
            _ = trie.ins(2usize, z());

            let mut buff = String::new();
            let mut test = Vec::new();

            let branches = trie.root.branches.as_mut().unwrap();
            ext(branches, &mut buff, &mut test);

            let proof = vec![(String::from("a"), 1), (String::from("z"), 2)];
            assert_eq!(proof.len(), test.len());
            test.sort_by_key(|x| x.0.clone());

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
                _ = trie.ins(e.1, e.0.chars());
            }

            let mut buff = String::new();
            let mut test = Vec::new();

            let branches = trie.root.branches.as_mut().unwrap();
            ext(branches, &mut buff, &mut test);

            assert_eq!(entries.len(), test.len());

            test.sort_by_key(|x| x.clone());
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

            let branches = trie.root.branches.as_mut().unwrap();
            ext(branches, &mut buff, &mut test);

            assert_eq!(paths.len(), test.len());

            test.sort_by_key(|x| x.clone());
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

            let branches = unsafe { trie.root.branches.as_ref().unwrap_unchecked() };
            view(branches, &mut buff, &mut test);

            let proof = vec![(String::from("a"), &a_entry), (String::from("z"), &z_entry)];

            assert_eq!(proof.len(), test.len());

            test.sort_by_key(|x| x.0.clone());
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

            let branches = unsafe { trie.root.branches.as_ref().unwrap_unchecked() };
            view(branches, &mut buff, &mut test);

            assert_eq!(entries.len(), test.len());

            test.sort_by_key(|x| x.0.clone());
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

            let branches = unsafe { trie.root.branches.as_ref().unwrap_unchecked() };
            view(branches, &mut buff, &mut test);

            assert_eq!(paths.len(), test.len());
            test.sort_by_key(|x| x.0.clone());

            assert_eq!(paths, test);
        }
    }

    mod trie {
        use crate::Trie;

        #[test]
        fn new() {
            let trie = Trie::<usize>::new();

            let root = &trie.root;
            assert_eq!(false, root.entry());
            assert_eq!(None, root.branches);
            assert_eq!(0, trie.cnt);

            let btr = &trie.btr;
            assert_eq!(0, btr.len());
            assert_eq!(0, btr.capacity());
        }

        mod ins {
            use crate::{KeyErr, Trie};

            #[test]
            fn zero_length_key() {
                let mut trie = Trie::new();
                let proof = Err(KeyErr::ZeroLen);
                let test = trie.ins(0usize, "".chars());
                assert_eq!(proof, test);
                assert_eq!(0, trie.cnt);
            }

            #[test]
            fn basic_test() {
                const KEY: &str = "touchstone";

                let mut trie = Trie::new();
                let res = trie.ins(3usize, KEY.chars());
                assert_eq!(Ok((&mut 3, None)), res);

                let branches = &trie.root.branches.as_ref();
                assert_eq!(true, branches.is_some());
                let mut branches = branches.unwrap();

                let last_node_ix = KEY.len() - 1;
                for (ix, c) in KEY.chars().enumerate() {
                    let node = &branches.get(&c);

                    assert!(node.is_some());
                    let node = node.unwrap();

                    if ix == last_node_ix {
                        assert_eq!(false, node.branches());
                        assert_eq!(Some(3), node.entry);
                    } else {
                        assert_eq!(false, node.entry());
                        assert_eq!(true, node.branches());
                        branches = node.branches.as_ref().unwrap();
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
                assert_eq!(Ok((&mut exi_val, None)), res);
                assert_eq!(1, trie.cnt);

                let res = trie.ins(new_val, new());
                assert_eq!(Ok((&mut new_val, None)), res);
                assert_eq!(2, trie.cnt);

                assert_eq!(Ok(&exi_val), trie.acq(existing()));
                assert_eq!(Ok(&new_val), trie.acq(new()));
            }

            #[test]
            fn singular_key() {
                let mut entry = 3;

                let mut trie = Trie::new();
                let res = trie.ins(entry, "a".chars());
                assert_eq!(Ok((&mut entry, None)), res);
                assert_eq!(1, trie.cnt);

                let branches = trie.root.branches;
                assert_eq!(true, branches.is_some());
                let branches = branches.unwrap();
                let node = branches.get(&'a');
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
                assert_eq!(Ok((&mut entry_1, None)), res);
                assert_eq!(1, trie.cnt);

                let res = trie.ins(entry_2, keyer());
                assert_eq!(Ok((&mut entry_2, Some(entry_1))), res);
                assert_eq!(1, trie.cnt);

                let branches = &trie.root.branches.as_ref();
                assert_eq!(true, branches.is_some());
                let mut branches = branches.unwrap();

                let last_ix = key.len() - 1;
                for (ix, c) in keyer().enumerate() {
                    let node = branches.get(&c);
                    assert_eq!(true, node.is_some());
                    let node = node.unwrap();

                    if ix == last_ix {
                        assert_eq!(false, node.branches());
                        assert_eq!(Some(entry_2), node.entry)
                    } else {
                        assert_eq!(true, node.branches());
                        branches = node.branches.as_ref().unwrap();
                    }
                }
            }
        }

        mod acq {

            use crate::{KeyErr, Trie};

            #[test]
            fn member() {
                let key = || "Keyword".chars();
                let mut trie = Trie::new();
                _ = trie.ins(27usize, key());

                let res = trie.acq(key());
                assert_eq!(Ok(&27), res);
            }

            #[test]
            fn not_member() {
                let key = "Keyword";
                let mut trie = Trie::new();
                _ = trie.ins(0usize, key.chars());

                for key in ["Key", "Opener"] {
                    let res = trie.acq(key.chars());
                    assert_eq!(Err(KeyErr::Unknown), res);
                }
            }

            #[test]
            fn zero_length_key() {
                let trie = Trie::<usize>::new();
                let res = trie.acq("".chars());
                assert_eq!(Err(KeyErr::ZeroLen), res);
            }
        }

        mod acq_mut {

            use crate::{KeyErr, Trie};

            #[test]
            fn member() {
                let key = || "Keyword".chars();
                let mut trie = Trie::new();
                _ = trie.ins(27usize, key());

                let res = trie.acq_mut(key());
                assert_eq!(Ok(&mut 27), res);
            }

            #[test]
            fn not_member() {
                let key = "Keyword";
                let mut trie = Trie::new();
                _ = trie.ins(0usize, key.chars());

                for key in ["Key", "Opener"] {
                    let res = trie.acq_mut(key.chars());
                    assert_eq!(Err(KeyErr::Unknown), res);
                }
            }

            #[test]
            fn zero_length_key() {
                let mut trie = Trie::<usize>::new();
                let res = trie.acq_mut("".chars());
                assert_eq!(Err(KeyErr::ZeroLen), res);
            }
        }

        mod rem {
            use crate::{KeyErr, Trie};

            #[test]
            fn known_unknown() {
                let known = || "safe-hideaway".chars();
                let unknown = || "grave-monition".chars();

                let mut trie = Trie::new();

                let known_entry = 13;
                _ = trie.ins(known_entry, known());

                assert_eq!(Err(KeyErr::Unknown), trie.rem(unknown()));
                assert_eq!(0, trie.btr.len());
                assert_eq!(1, trie.cnt);

                assert_eq!(Ok(known_entry), trie.rem(known()));
                assert_eq!(0, trie.btr.len());
                assert_eq!(0, trie.cnt);
                assert_eq!(Err(KeyErr::Unknown), trie.acq(known()));
            }

            #[test]
            fn zero_length_key() {
                let mut trie = Trie::<usize>::new();
                let res = trie.rem("".chars());
                assert_eq!(Err(KeyErr::ZeroLen), res);
            }
        }

        // node in path to entry being deleted cannot
        // be deleted if and only if participates in
        // path to another entry where path len varies 0…m
        mod rem_actual {

            use crate::{KeyErr, TraStrain, Trie};

            #[test]
            fn basic_test() {
                let key = || "abcxyz".chars();
                let entry = 60;

                let mut trie = Trie::new();
                _ = trie.ins(entry, key());
                _ = trie.track(key(), TraStrain::TraEmp);

                assert_eq!(entry, trie.rem_actual(&mut 0));
                assert_eq!(Err(KeyErr::Unknown), trie.acq(key()));
            }

            #[test]
            fn one_letter_a() {
                let key = || "a".chars();
                let entry = 60;

                let mut trie = Trie::new();
                _ = trie.ins(entry, key());
                _ = trie.track(key(), TraStrain::TraEmp);

                let mut esc_code = 0;
                assert_eq!(entry, trie.rem_actual(&mut esc_code));
                assert_eq!(Err(KeyErr::Unknown), trie.acq(key()));
                assert_eq!(18, esc_code);
                assert_eq!(false, trie.root.branches());
            }

            #[test]
            fn one_letter_b() {
                let key1 = || "a".chars();
                let key2 = || "b".chars();
                let entry1 = 50;
                let entry2 = 60;

                let mut trie = Trie::new();
                _ = trie.ins(entry1, key1());
                _ = trie.ins(entry2, key2());
                _ = trie.track(key1(), TraStrain::TraEmp);

                let mut esc_code = 0;
                assert_eq!(entry1, trie.rem_actual(&mut esc_code));
                assert_eq!(Err(KeyErr::Unknown), trie.acq(key1()));
                assert_eq!(Ok(&entry2), trie.acq(key2()));
                assert_eq!(6, esc_code);
            }

            #[test]
            fn one_letter_c() {
                let key1 = || "a".chars();
                let key2 = || "al".chars();

                let entry1 = 50;
                let entry2 = 60;

                let mut trie = Trie::new();
                _ = trie.ins(entry1, key1());
                _ = trie.ins(entry2, key2());

                _ = trie.track(key1(), TraStrain::TraEmp);

                let mut esc_code = 0;
                assert_eq!(entry1, trie.rem_actual(&mut esc_code));
                assert_eq!(Err(KeyErr::Unknown), trie.acq(key1()));
                assert_eq!(Ok(&entry2), trie.acq(key2()));
                assert_eq!(1, esc_code);
            }

            #[test]
            fn inner_entry() {
                let mut trie = Trie::new();

                let outer = || "Keyword".chars();
                _ = trie.ins(0usize, outer());

                let inner = || "Key".chars();
                _ = trie.ins(1usize, inner());

                let mut esc_code = 0;
                _ = trie.track(inner(), TraStrain::TraEmp);

                assert_eq!(1, trie.rem_actual(&mut esc_code));
                assert_eq!(1, esc_code);

                assert_eq!(Err(KeyErr::Unknown), trie.acq(inner()));
                assert_eq!(true, trie.acq(outer()).is_ok());
            }

            #[test]
            fn branches_removal() {
                let key = || "Keyword".chars();
                let mut trie = Trie::new();
                _ = trie.ins(1usize, key());

                let mut esc_code = 0;
                _ = trie.track(key(), TraStrain::TraEmp);
                assert_eq!(1, trie.rem_actual(&mut esc_code));
                assert_eq!(18, esc_code);

                assert_eq!(Err(KeyErr::Unknown), trie.acq(key()));
                assert_eq!(None, trie.root.branches);
            }

            #[test]
            fn node_composing_path() {
                let dissimilar = || "Dissimilar".chars();
                let keyword = || "Keyword".chars();

                let mut trie = Trie::new();
                _ = trie.ins(0usize, dissimilar());
                _ = trie.ins(1usize, keyword());

                let mut esc_code = 0;
                _ = trie.track(keyword(), TraStrain::TraEmp);
                assert_eq!(1, trie.rem_actual(&mut esc_code));
                assert_eq!(6, esc_code);

                assert_eq!(Err(KeyErr::Unknown), trie.acq(keyword()));
                assert_eq!(true, trie.acq(dissimilar()).is_ok());
            }

            #[test]
            fn entry_under_entry() {
                let above = || "keyworder".chars();
                let under = || "keyworders".chars();
                let mut trie = Trie::new();
                _ = trie.ins(0usize, above());
                _ = trie.ins(1usize, under());

                let mut esc_code = 0;
                _ = trie.track(under(), TraStrain::TraEmp);
                assert_eq!(1, trie.rem_actual(&mut esc_code));
                assert_eq!(10, esc_code);

                assert_eq!(Err(KeyErr::Unknown), trie.acq(under()));
                assert_eq!(true, trie.acq(above()).is_ok());

                _ = trie.track(above(), TraStrain::TraEmp);
                let btr = &trie.btr;
                let last = btr[btr.len() - 1];
                assert_eq!('r', last.0);
                let node = unsafe { last.1.as_ref() }.unwrap();
                assert_eq!(false, node.branches());
            }
        }

        mod track {

            use crate::{TraRes, TraStrain, Trie, NULL};

            #[test]
            fn tracing() {
                let mut trie = Trie::<usize>::new();

                let duos = [("k", 12), ("key", 22), ("keyword", 45)];
                for (k, e) in duos {
                    _ = trie.ins(e, k.chars());
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
                    _ => panic!("Not `TraRes::Ok`, but {:?}.", res),
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
                    _ => panic!("Not `TraRes::OkRef(_)`, but {:?}.", res),
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
                    _ => panic!("Not `TraRes::OkMut(_)`, but {:?}.", res),
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
                let trie = Trie::<usize>::new();
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
                assert_eq!(TraRes::UnknownForAbsentPathBranches, res);
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
            use crate::{uc::UC, Trie};

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
                trie.btr = UC::new(Vec::with_capacity(old_cap));

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
                b_tr.get_mut().reserve_exact(approx_cap);
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
            b_tr.get_mut().reserve_exact(cap);
            let cap = b_tr.capacity();

            assert_eq!(cap, trie.acq_trace_cap());
        }

        use crate::{KeyErr, Node};

        #[test]
        fn clr() {
            let key = "Key".chars();
            let mut trie = Trie::new();

            _ = trie.ins(77usize, key.clone());

            let mut cap = 50;
            assert!(trie.acq_trace_cap() < cap);
            cap = trie.put_trace_cap(cap);

            assert_eq!(1, trie.clr());
            assert_eq!(Err(KeyErr::Unknown), trie.acq(key));
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

                let mut trie = Trie::new();
                for p in proof.iter() {
                    _ = trie.ins(p.1, p.0.chars());
                }

                let ext = trie.ext();
                assert_eq!(true, ext.is_some());
                let mut ext = ext.unwrap();

                assert_eq!(proof.len(), ext.len());

                ext.sort_by_key(|x| x.0.clone());
                assert_eq!(proof, ext);

                assert_eq!(true, ext.capacity() >= 1000);

                for p in proof.iter() {
                    assert_eq!(Err(KeyErr::Unknown), trie.acq(p.0.chars()));
                }
            }

            #[test]
            fn empty_tree() {
                let mut trie = Trie::<usize>::new();
                let ext = trie.ext();

                assert_eq!(None, ext);
            }
        }

        mod view {

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

                let mut trie = Trie::new();
                for p in proof.iter() {
                    _ = trie.ins(*p.1, p.0.chars());
                }

                let view = trie.view();
                assert_eq!(true, view.is_some());
                let mut view = view.unwrap();

                assert_eq!(proof.len(), view.len());

                view.sort_by_key(|x| x.0.clone());
                assert_eq!(proof, view);

                assert_eq!(true, view.capacity() >= 1000);

                for p in proof.iter() {
                    assert_eq!(Ok(p.1), trie.acq(p.0.chars()));
                }
            }

            #[test]
            fn empty_tree() {
                let trie = Trie::<usize>::new();
                let view = trie.view();

                assert_eq!(None, view);
            }
        }

        mod as_ref {
            use crate::aide::address;
            use crate::Trie;

            #[test]
            fn empty_tree() {
                let trie = Trie::<usize>::new();
                let as_ref = trie.as_ref();
                assert_eq!(None, as_ref);
            }

            #[test]
            fn non_empty_tree() {
                let mut trie = Trie::new();
                _ = trie.ins(0, "0".chars());

                let as_ref = address(trie.as_ref().unwrap());
                let proof = address(trie.root.branches.as_ref().unwrap());

                assert_eq!(as_ref, proof);
            }
        }

        mod as_mut {
            use crate::aide::address;
            use crate::Trie;

            #[test]
            fn empty_tree() {
                let mut trie = Trie::<usize>::new();
                let as_mut = trie.as_mut();
                assert_eq!(None, as_mut);
            }

            #[test]
            fn non_empty_tree() {
                let mut trie = Trie::new();
                _ = trie.ins(0, "0".chars());

                let as_mut = address(trie.as_mut().unwrap());
                let proof = address(trie.root.branches.as_mut().unwrap());

                assert_eq!(as_mut, proof);
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
                TraRes::<u8>::UnknownForAbsentPathBranches.key_err()
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

        use crate::{Branches, Node};

        #[test]
        fn entry() {
            let mut node = Node::<usize>::empty();

            assert!(!node.entry());
            node.entry = Some(1);
            assert!(node.entry());
        }

        #[test]
        fn branches() {
            let mut node = Node::<usize>::empty();

            assert!(!node.branches());
            node.branches = Some(Branches::new());
            assert!(node.branches());
        }

        #[test]
        fn empty() {
            let node = Node::<usize>::empty();

            assert!(node.branches.is_none());
            assert!(node.entry.is_none());
        }

        use crate::aide::address;
        #[test]
        fn to_mut_ptr() {
            let n = Node::<usize>::empty();
            let n_add = address(&n);
            assert_eq!(n_add, n.to_mut_ptr() as usize);
        }
    }

    mod readme {
        use crate::{KeyErr, Trie};

        #[test]
        fn test() {
            let mut trie = Trie::<char>::new();

            let some = "información meteorológica".chars();
            _ = trie.ins('🌩', some.clone());

            let one_more = "alimentación RSS".chars();
            _ = trie.ins('😋', one_more.clone());

            assert_eq!(Ok('😋'), trie.rem(one_more.clone()));
            assert_eq!(Err(KeyErr::Unknown), trie.acq(one_more.clone()));

            let res = trie.acq_mut(some.clone());
            assert_eq!(Ok(&mut '🌩'), res);
            let entry = res.unwrap();
            *entry = '🌞';

            assert_eq!(Ok(&'🌞'), trie.acq(some.clone()));
        }
    }
}

// cargo fmt && cargo test --release
