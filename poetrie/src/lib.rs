//! Poetrie, poetic trie, is trie designated for finding rhymes for your verses.
//!
//! For given input, and populated tree, it will find word with lengthiest shared suffix for you.
// improvements:
//      - return n (10, max 10, …) words with x-length shared suffix
//      - allow to speficy expected min a max suffix match length
//      - custom letter equalizer
//      - use verbose method names
//      - case insensivity
// check 'imp:' also
use std::{collections::hash_map::HashMap, ops::Deref};

mod uc;
use uc::UC;

type Links = HashMap<char, Node>;

fn ext(l: &Links, buff: &mut Vec<char>, o: &mut Vec<String>) {
    for (k, n) in l.iter() {
        buff.push(*k);

        if n.entry {
            let entry = buff.iter().rev().collect();
            o.push(entry);
        }

        if let Some(l) = n.links.as_ref() {
            ext(l, buff, o);
        }

        _ = buff.pop();
    }
}

/// `Entry` alias for using in key role.
pub type Key<'a> = Entry<'a>;

/// `&str` validated for usage with `Poetrie`.
#[derive(Clone, PartialEq, Debug)]
pub struct Entry<'a>(&'a str);

impl<'a> Entry<'a> {
    /// Constructor for `Entry<'a>`.
    ///
    /// Return value is `None` for 0-length `str`.
    pub const fn new_from_str(entry: &'a str) -> Option<Self> {
        if entry.len() == 0 {
            None
        } else {
            Some(Entry(entry))
        }
    }
}

impl<'a> Deref for Entry<'a> {
    type Target = str;

    fn deref(&self) -> &str {
        &self.0
    }
}

/// Poetrie is poetic retrieval tree implementation for finding words with shared suffixes.
///
/// Inputs are validated only for 0 length thus is up to consumer code
/// to allow population with sensible values only.
///
/// All methods are case sensitive.
pub struct Poetrie {
    root: Node,
    // backtrace buff
    btr: UC<Vec<(char, *mut Node)>>,
    // sufix-word buffer
    buf: UC<Vec<char>>,
    // entries count
    cnt: usize,
}

const NULL: char = '\0';
impl Poetrie {
    /// Use for `Poetrie` construction.    
    pub const fn new() -> Poetrie {
        Poetrie {
            root: Node::empty(),
            btr: UC::new(Vec::new()),
            buf: UC::new(Vec::new()),
            cnt: 0,
        }
    }

    /// Use for entry insertions into tree.
    ///
    /// Return value is `true` if entry was inserted into tree,
    /// `false` if it was present already.
    pub fn ins(&mut self, entry: &Entry) -> bool {
        let mut node = &mut self.root;
        let mut chars = entry.chars();
        while let Some(c) = chars.next_back() {
            let links = node.links.get_or_insert_with(|| Links::new());
            node = links.entry(c).or_insert(Node::empty());
        }

        if node.entry {
            false
        } else {
            node.entry = true;
            self.cnt += 1;

            true
        }
    }

    /// Use to verify entry presence in tree.
    ///
    /// Return value is `true` if entry is present in tree, `false` otherwise.
    pub fn en(&self, entry: &Key) -> bool {
        let res = self.track(entry, false);

        TraRes::Ok == res
    }

    /// Use to find entry with most shared suffix to key.
    ///
    /// If there are more entries with equal suffix length,
    /// only one in unguaranteed precedence is returned.    
    pub fn suf(&self, key: &Key) -> Result<String, FindErr> {
        let res = self.find(
            key,
            #[cfg(test)]
            &mut 0,
        );

        self.buf.get_mut().clear();

        return res;
    }

    /// Use to remove entry from tree.
    ///
    /// Return value is `true` if entry was removed, `false` if it was not present.
    pub fn rem(&mut self, entry: &Entry) -> bool {
        let tra_res = self.track(entry, true);
        let res = if let TraRes::Ok = tra_res {
            self.rem_actual(
                #[cfg(test)]
                &mut 0,
            );

            self.cnt -= 1;
            true
        } else {
            false
        };

        self.btr.get_mut().clear();
        res
    }

    fn rem_actual(&mut self, #[cfg(test)] esc_code: &mut usize) {
        let mut trace = self.btr.iter();
        let en_duo = unsafe { trace.next_back().unwrap_unchecked() };
        let mut node = unsafe { en_duo.1.as_mut().unwrap_unchecked() };

        node.entry = false;
        if node.links() {
            #[cfg(test)]
            set_code(1, esc_code);

            return;
        }

        // subnode entry
        let mut sn_entry = &en_duo.0;
        while let Some((c, n)) = trace.next_back() {
            node = unsafe { n.as_mut().unwrap_unchecked() };
            let links = unsafe { node.links.as_mut().unwrap_unchecked() };
            _ = links.remove(sn_entry);

            #[cfg(test)]
            set_code(2, esc_code);

            if links.len() > 0 {
                #[cfg(test)]
                set_code(4, esc_code);

                return;
            }

            if node.entry {
                #[cfg(test)]
                set_code(8, esc_code);

                break;
            }

            sn_entry = c;
        }

        node.links = None;
        #[cfg(test)]
        if *esc_code != (2 | 8) {
            set_code(16, esc_code);
        }

        #[cfg(test)]
        fn set_code(c: usize, esc_code: &mut usize) {
            let code = *esc_code;
            *esc_code = code | c;
        }
    }

    // case-sensitive which is not senseful
    fn find(&self, key: &Key, #[cfg(test)] b_code: &mut usize) -> Result<String, FindErr> {
        let mut chars = key.chars();
        let mut c;

        // match
        let buff = self.buf.get_mut();

        // operative node
        let mut op_node = &self.root;
        if let Some(l) = op_node.links.as_ref() {
            c = unsafe { chars.next_back().unwrap_unchecked() };
            if let Some(n) = l.get(&c) {
                op_node = n;
                buff.push(c)
            } else {
                return Err(FindErr::NoJointSuffix);
            }
        } else {
            return Err(FindErr::EmptyTree);
        }

        // closest branch information
        let mut branching = None;
        let mut bak_len = 0;

        // track key as much as possible first
        'track: loop {
            if let Some(next_c) = chars.next_back() {
                if op_node.entry {
                    bak_len = buff.len();
                }

                c = next_c;
            } else {
                #[cfg(test)]
                set_bcode(2, b_code);
                break 'track;
            };

            if let Some(l) = op_node.links.as_ref() {
                if let Some(n) = l.get(&c) {
                    if l.len() > 1 {
                        branching = Some((l, (buff.len(), c)));
                    }

                    buff.push(c);
                    op_node = n;

                    continue;
                }

                #[cfg(test)]
                set_bcode(4, b_code);
                break 'track;
            }

            #[cfg(test)]
            set_bcode(8, b_code);
            break 'track;
        }

        // CONTINUATION
        // A) Is possible (key covers partially some entry):
        // - (1) Key is suffix to some entry.
        // - (2) Key has partially shared suffix with some entry.
        //
        // B) Not possible (key just convers fully some entry):
        // - (1) Key is entry and no suffix to other entry.
        // - (2) Part of key suffix is other entry.
        //
        // Note: When A then A can intersect with B, when B then B only.
        if !op_node.links.is_some() {
            if let Some((blinks, (blen, skip_c))) = branching {
                // just subentry with longer shared suffix
                // must be prioritized over branch
                if bak_len > blen {
                    #[cfg(test)]
                    set_bcode(256, b_code);
                    return ok(&buff[..bak_len]);
                }

                #[cfg(test)]
                set_bcode(512, b_code);

                buff.truncate(blen);

                // imp: possibly randomize somehow node selection
                for (&test_c, n) in blinks.iter() {
                    if test_c == skip_c {
                        continue;
                    }

                    buff.push(test_c);
                    op_node = n;
                    break;
                }
            } else {
                return if bak_len == 0 {
                    #[cfg(test)]
                    set_bcode(16, b_code);
                    Err(FindErr::OnlyKeyMatches)
                } else {
                    #[cfg(test)]
                    set_bcode(32, b_code);
                    ok(&buff[..bak_len])
                };
            }
        }

        while let Some(l) = op_node.links.as_ref() {
            // imp: possibly randomize hashmap key selection
            let (c, n) = unsafe { l.iter().next().unwrap_unchecked() };
            buff.push(*c);
            op_node = n;
        }

        #[cfg(test)]
        set_bcode(128, b_code);
        return ok(&buff);

        fn ok(cs: &[char]) -> Result<String, FindErr> {
            return Ok(cs.iter().rev().collect());
        }

        #[cfg(test)]
        fn set_bcode(c: usize, b_code: &mut usize) {
            let code = *b_code;
            *b_code = code | c;
        }
    }

    fn track(&self, entry: &Key, trace: bool) -> TraRes {
        let mut node = &self.root;
        let btr = self.btr.get_mut();

        if trace {
            btr.push((NULL, node.to_mut_ptr()));
        }

        let mut chars = entry.chars();
        while let Some(c) = chars.next_back() {
            if let Some(l) = node.links.as_ref() {
                if let Some(n) = l.get(&c) {
                    if trace {
                        btr.push((c, n.to_mut_ptr()));
                    }

                    node = n;
                    continue;
                }
                return TraRes::UnknownForAbsentPathNode;
            }

            return TraRes::UnknownForAbsentPathLinks;
        }

        if node.entry {
            TraRes::Ok
        } else {
            TraRes::UnknownForNotEntry
        }
    }

    /// Use to obtain count of entries in tree.
    pub const fn ct(&self) -> usize {
        self.cnt
    }

    /// Use to extract entries from tree.
    ///
    /// Extraction is alphabetically unordered. Leaves tree intact.
    ///
    /// Return value is `None` for empty `Poetrie`.    
    pub fn ext(&mut self) -> Option<Vec<String>> {
        if self.cnt == 0 {
            return None;
        }

        // capacity is prebuffered to 1000
        let mut buff = Vec::with_capacity(1000);

        // capacity is prebuffered to 5000
        let mut res = Vec::with_capacity(5000);

        let rl = unsafe { self.root.links.as_ref().unwrap_unchecked() };
        ext(rl, &mut buff, &mut res);

        Some(res)
    }
}

#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq)]
enum TraRes {
    Ok,
    UnknownForNotEntry,
    UnknownForAbsentPathLinks,
    UnknownForAbsentPathNode,
}

#[derive(Debug, PartialEq, Clone)]
/// Various errors which can occur when searching common suffix.
pub enum FindErr {
    /// Key provided has only one match in tree, itself.
    OnlyKeyMatches,
    /// Tree is empty.
    EmptyTree,
    /// No entry shares any sufix with key.
    NoJointSuffix,
}

struct Node {
    links: Option<Links>,
    entry: bool,
}

impl Node {
    const fn links(&self) -> bool {
        self.links.is_some()
    }

    const fn empty() -> Self {
        Node {
            links: None,
            entry: false,
        }
    }

    const fn to_mut_ptr(&self) -> *mut Self {
        (self as *const Self).cast_mut()
    }
}

#[cfg(test)]
impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        self as *const Self == other as *const Self
    }
}

#[cfg(test)]
use std::fmt::{Debug, Formatter};

#[cfg(test)]
impl Debug for Node {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let links = if self.links() { "Some" } else { "None" };

        f.write_fmt(format_args!(
            "Node {{\n  links: {}\n  entry: {}\n}}",
            links, self.entry
        ))
    }
}

#[cfg(test)]
mod tests_of_units {

    mod rev_entry {
        use crate::Entry;

        pub struct RevEntry(pub String);

        impl RevEntry {
            pub fn new(e: &str) -> Self {
                let rev = e.chars().rev().collect();
                RevEntry(rev)
            }

            pub fn entry(&self) -> Entry {
                Entry(self.0.as_str())
            }
        }

        use std::ops::Deref;
        impl Deref for RevEntry {
            type Target = String;
            fn deref(&self) -> &String {
                &self.0
            }
        }
    }

    mod ext {

        use crate::{Entry, Poetrie, ext};

        #[test]
        fn basic_test() {
            let mut poetrie = Poetrie::new();

            let a = &Entry("a");
            let z = &Entry("z");

            _ = poetrie.ins(a);
            _ = poetrie.ins(z);

            let mut buff = Vec::new();
            let mut test = Vec::new();

            let links = poetrie.root.links.as_mut().unwrap();
            ext(links, &mut buff, &mut test);

            let proof = vec![String::from("a"), String::from("z")];
            assert_eq!(proof.len(), test.len());
            test.sort();

            assert_eq!(proof, test);

            assert_eq!(true, poetrie.en(a));
            assert_eq!(true, poetrie.en(z));
        }

        #[test]
        fn nesting() {
            let mut poetrie = Poetrie::new();

            let entries = vec![
                String::from("a"),
                String::from("az"),
                String::from("b"),
                String::from("by"),
                String::from("y"),
                String::from("yb"),
                String::from("z"),
                String::from("za"),
            ];

            for e in entries.iter() {
                _ = poetrie.ins(&Entry(e.as_str()));
            }

            let mut buff = Vec::new();
            let mut test = Vec::new();

            let links = poetrie.root.links.as_mut().unwrap();
            ext(links, &mut buff, &mut test);

            assert_eq!(entries.len(), test.len());

            test.sort();
            assert_eq!(entries, test);
        }

        #[test]
        fn in_depth_recursion() {
            let mut poetrie = Poetrie::new();

            let paths = vec![
                String::from("aa"),
                String::from("azbq"),
                String::from("by"),
                String::from("ybc"),
                String::from("ybcrqutmop"),
                String::from("ybcrqutmopfvb"),
                String::from("ybcrqutmoprfg"),
                String::from("ybxr"),
                String::from("zazazazazabyyb"),
            ];

            for p in paths.iter() {
                _ = poetrie.ins(&Entry(p.as_str()));
            }

            let mut buff = Vec::new();
            let mut test = Vec::new();

            let links = poetrie.root.links.as_mut().unwrap();
            ext(links, &mut buff, &mut test);

            assert_eq!(paths.len(), test.len());

            test.sort();
            assert_eq!(paths, test);
        }
    }

    mod entry {
        use crate::Entry;
        use std::ops::Deref;

        #[test]
        fn new_from_str() {
            let entry = "entry";
            let test = Entry::new_from_str(entry);
            assert_eq!(true, test.is_some());
            assert_eq!(entry.as_ptr() as usize, test.unwrap().0.as_ptr() as usize);
        }

        #[test]
        fn new_from_str_zero_entry() {
            let entry = "";
            let test = Entry::new_from_str(entry);
            assert_eq!(None, test);
        }

        #[test]
        fn deref() {
            let entry = "entry";
            let test = Entry(entry);
            assert_eq!(entry, test.deref());
        }
    }

    mod poetrie {
        use crate::Poetrie;

        #[test]
        fn new() {
            let poetrie = Poetrie::new();

            let root = poetrie.root;
            assert_eq!(false, root.entry);
            assert_eq!(None, root.links);
            assert_eq!(0, poetrie.cnt);

            let btr = poetrie.btr;
            assert_eq!(0, btr.len());
            assert_eq!(0, btr.capacity());

            let buf = poetrie.buf;
            assert_eq!(0, buf.len());
            assert_eq!(0, buf.capacity());
        }

        mod ins {
            use crate::{Entry, Poetrie};

            #[test]
            fn basic_test() {
                let entry = Entry("touchstone");

                let mut poetrie = Poetrie::new();
                let res = poetrie.ins(&entry);
                assert_eq!(true, res);

                let links = &poetrie.root.links.as_ref();
                assert_eq!(true, links.is_some());
                let mut links = links.unwrap();

                let last_node_ix = entry.len() - 1;
                for (ix, c) in entry.chars().rev().enumerate() {
                    let node = &links.get(&c);

                    assert!(node.is_some());
                    let node = node.unwrap();

                    if ix == last_node_ix {
                        assert_eq!(false, node.links());
                        assert_eq!(true, node.entry);
                    } else {
                        assert_eq!(false, node.entry);
                        assert_eq!(true, node.links());
                        links = node.links.as_ref().unwrap();
                    }
                }

                assert_eq!(1, poetrie.cnt);
            }

            #[test]
            fn existing_path_insert() {
                let existing = &Entry("touchstone");
                let new = &Entry("touch");

                let mut poetrie = Poetrie::new();

                let res = poetrie.ins(existing);
                assert_eq!(true, res);
                assert_eq!(1, poetrie.cnt);

                let res = poetrie.ins(new);
                assert_eq!(true, res);
                assert_eq!(2, poetrie.cnt);

                assert_eq!(true, poetrie.en(existing));
                assert_eq!(true, poetrie.en(new));
            }

            #[test]
            fn singular_entry() {
                let e = Entry("a");

                let mut poetrie = Poetrie::new();
                let res = poetrie.ins(&e);
                assert_eq!(true, res);
                assert_eq!(1, poetrie.cnt);

                let links = poetrie.root.links;
                assert_eq!(true, links.is_some());
                let links = links.unwrap();
                let node = links.get(&'a');
                assert_eq!(true, node.is_some());
                assert_eq!(true, node.unwrap().entry);
            }

            #[test]
            fn double_insert() {
                let entry = &Entry("appealing delicacy");

                let mut poetrie = Poetrie::new();
                let res = poetrie.ins(&entry);
                assert_eq!(true, res);
                assert_eq!(1, poetrie.cnt);

                let res = poetrie.ins(&entry);
                assert_eq!(false, res);
                assert_eq!(1, poetrie.cnt);

                let links = &poetrie.root.links.as_ref();
                assert_eq!(true, links.is_some());
                let mut links = links.unwrap();

                let last_ix = entry.len() - 1;
                for (ix, c) in entry.chars().rev().enumerate() {
                    let node = links.get(&c);
                    assert_eq!(true, node.is_some());
                    let node = node.unwrap();

                    if ix == last_ix {
                        assert_eq!(false, node.links());
                        assert_eq!(true, node.entry)
                    } else {
                        assert_eq!(true, node.links());
                        assert_eq!(false, node.entry);
                        links = node.links.as_ref().unwrap();
                    }
                }
            }
        }

        mod en {

            use crate::{Entry, Poetrie};

            #[test]
            fn member() {
                let e = &Entry("Keyword");
                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(e);

                let res = poetrie.en(e);
                assert_eq!(true, res);
            }

            #[test]
            fn not_member() {
                let e = &Entry("Keyword");
                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(e);

                for e in ["Key", "Opener"] {
                    let e = Entry(e);
                    let res = poetrie.en(&e);
                    assert_eq!(false, res);
                }
            }
        }

        mod suf {
            use crate::{Entry, FindErr, Poetrie};

            #[test]
            fn basic_test() {
                let mut poetrie = Poetrie::new();

                let proof = String::from("quadriliteral");
                let entry = Entry(proof.as_str());
                _ = poetrie.ins(&entry);

                let key = Entry("semiliteral");
                let res = poetrie.suf(&key);
                assert_eq!(Ok(proof), res);
            }

            #[test]
            fn err() {
                let poetrie = Poetrie::new();

                let key = Entry("semiliteral");
                let res = poetrie.suf(&key);
                assert_eq!(Err(FindErr::EmptyTree), res);
            }

            #[test]
            fn buf_clearing() {
                let mut poetrie = Poetrie::new();

                let key_entry = Entry("quadriliteral");
                _ = poetrie.ins(&key_entry);

                let res = poetrie.suf(&key_entry);
                assert_eq!(Err(FindErr::OnlyKeyMatches), res);
                assert_eq!(0, poetrie.buf.len());
                assert_eq!(true, poetrie.buf.capacity() > 0);
            }
        }

        mod rem {
            use crate::{Entry, Poetrie};

            #[test]
            fn known_unknown() {
                let known = &Entry("safe-hideaway");
                let unknown = &Entry("grave-monition");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(known);

                assert_eq!(false, poetrie.rem(unknown));
                assert_eq!(0, poetrie.btr.len());
                assert_eq!(true, poetrie.btr.capacity() > 0);
                assert_eq!(1, poetrie.cnt);

                assert_eq!(true, poetrie.rem(known));
                assert_eq!(0, poetrie.btr.len());
                assert_eq!(0, poetrie.cnt);
                assert_eq!(false, poetrie.en(known));
            }
        }

        // node in path to entry being deleted cannot
        // be deleted if and only if participates in
        // path to another entry where path len varies 0…m
        mod rem_actual {

            use super::super::rev_entry::RevEntry;
            use crate::{Entry, Poetrie};

            #[test]
            fn basic_test() {
                let entry = RevEntry::new("abcxyz");
                let entry = &entry.entry();

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(entry);
                _ = poetrie.track(entry, true);

                poetrie.rem_actual(&mut 0);
                assert_eq!(false, poetrie.en(entry));
            }

            #[test]
            fn one_letter_a() {
                let entry = &Entry("a");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(entry);
                _ = poetrie.track(entry, true);

                let mut esc_code = 0;
                poetrie.rem_actual(&mut esc_code);
                assert_eq!(false, poetrie.en(entry));
                assert_eq!(18, esc_code);
            }

            #[test]
            fn one_letter_b() {
                let entry1 = &Entry("a");
                let entry2 = &Entry("b");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(entry1);
                _ = poetrie.ins(entry2);
                _ = poetrie.track(entry1, true);

                let mut esc_code = 0;
                poetrie.rem_actual(&mut esc_code);
                assert_eq!(false, poetrie.en(entry1));
                assert_eq!(true, poetrie.en(entry2));
                assert_eq!(6, esc_code);
            }

            #[test]
            fn one_letter_c() {
                let entry1 = &Entry("a");
                let entry2 = RevEntry::new("al");
                let entry2 = &entry2.entry();

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(entry1);
                _ = poetrie.ins(entry2);
                _ = poetrie.track(entry1, true);

                let mut esc_code = 0;
                poetrie.rem_actual(&mut esc_code);
                assert_eq!(false, poetrie.en(entry1));
                assert_eq!(true, poetrie.en(entry2));
                assert_eq!(1, esc_code);
            }

            #[test]
            fn inner_entry() {
                let mut poetrie = Poetrie::new();

                let outer = RevEntry::new("Keyword");
                let outer = &outer.entry();
                _ = poetrie.ins(&outer);

                let inner = RevEntry::new("Key");
                let inner = &inner.entry();
                _ = poetrie.ins(inner);

                let mut esc_code = 0;
                _ = poetrie.track(inner, true);

                poetrie.rem_actual(&mut esc_code);
                assert_eq!(1, esc_code);

                assert_eq!(false, poetrie.en(inner));
                assert_eq!(true, poetrie.en(outer));
            }

            #[test]
            fn links_removal() {
                let entry = RevEntry::new("Keyword");
                let entry = &entry.entry();
                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(entry);

                let mut esc_code = 0;
                _ = poetrie.track(entry, true);
                poetrie.rem_actual(&mut esc_code);
                assert_eq!(18, esc_code);

                assert_eq!(false, poetrie.en(entry));
                assert_eq!(None, poetrie.root.links);
            }

            #[test]
            fn node_composing_path() {
                let dissimilar = RevEntry::new("Dissimilar");
                let dissimilar = &dissimilar.entry();
                let keyword = RevEntry::new("Keyword");
                let keyword = &keyword.entry();

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(dissimilar);
                _ = poetrie.ins(keyword);

                let mut esc_code = 0;
                _ = poetrie.track(keyword, true);
                poetrie.rem_actual(&mut esc_code);
                assert_eq!(6, esc_code);

                assert_eq!(false, poetrie.en(keyword));
                assert_eq!(true, poetrie.en(dissimilar));
            }

            #[test]
            fn entry_under_entry() {
                let above = RevEntry::new("keyworder");
                let above = &above.entry();
                let under = RevEntry::new("keyworders");
                let under = &under.entry();
                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(above);
                _ = poetrie.ins(under);

                let mut esc_code = 0;
                _ = poetrie.track(under, true);
                poetrie.rem_actual(&mut esc_code);
                assert_eq!(10, esc_code);

                assert_eq!(false, poetrie.en(under));
                assert_eq!(true, poetrie.en(above));

                _ = poetrie.track(above, true);
                let btr = &poetrie.btr;
                let last = btr[btr.len() - 1];
                assert_eq!('r', last.0);
                let node = unsafe { last.1.as_ref() }.unwrap();
                assert_eq!(false, node.links());
            }
        }

        mod find {
            use crate::{Entry, FindErr, Poetrie, tests_of_units::rev_entry::RevEntry};

            #[test]
            fn basic_test() {
                let proof = String::from("halieutics");
                let entry = &Entry(proof.as_str());

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(entry);
                _ = poetrie.ins(&Entry("codecs"));

                let key = &Entry("lyrics");
                let find = poetrie.find(key, &mut 0);

                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn exactly_last_match_1a() {
                let entry = &Entry("s");
                let key = &Entry("lyrics");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(entry);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(40, b_code);
                assert_eq!(Ok(String::from("s")), find);
            }

            #[test]
            fn exactly_last_match_1b() {
                let entry = &Entry("s");
                let key = &Entry("lyrics");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(entry);
                _ = poetrie.ins(key);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(34, b_code);
                assert_eq!(Ok(String::from("s")), find);
            }

            #[test]
            fn exactly_last_match_2a() {
                let proof = String::from("lyrics");
                let entry = &Entry(proof.as_str());
                let key = &Entry("s");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(entry);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(130, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn exactly_last_match_2b() {
                let proof = String::from("lyrics");
                let entry = &Entry(proof.as_str());
                let key = &Entry("s");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(entry);
                _ = poetrie.ins(key);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(130, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn exactly_last_match_3() {
                let key_entry = &Entry("s");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(key_entry);

                let mut b_code = 0;
                let find = poetrie.find(key_entry, &mut b_code);

                assert_eq!(18, b_code);
                assert_eq!(Err(FindErr::OnlyKeyMatches), find);
            }

            #[test]
            fn no_data() {
                let key = &Entry("lyrics");

                let poetrie = Poetrie::new();
                let find = poetrie.find(key, &mut 0);

                assert_eq!(Err(FindErr::EmptyTree), find);
            }

            #[test]
            fn no_suffix_match() {
                let entry = &Entry("epicalyx");
                let key = &Entry("lyrics");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(entry);

                let find = poetrie.find(key, &mut 0);

                assert_eq!(Err(FindErr::NoJointSuffix), find);
            }

            #[test]
            fn key_matches_itself_only() {
                let itself = &Entry("lyrics");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(itself);

                let mut b_code = 0;
                let find = poetrie.find(itself, &mut b_code);

                assert_eq!(18, b_code);
                assert_eq!(Err(FindErr::OnlyKeyMatches), find);
            }

            #[test]
            fn key_is_suffix_to_entry_1() {
                let subentry = RevEntry::new("document");
                let entry = RevEntry::new("documentalist");
                let proof = entry.0.clone();

                let key = RevEntry::new("documental");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(&subentry.entry());
                _ = poetrie.ins(&entry.entry());

                let mut b_code = 0;
                let find = poetrie.find(&key.entry(), &mut b_code);

                assert_eq!(130, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn key_is_suffix_to_entry_2() {
                let subentry = RevEntry::new("document");
                let entry = RevEntry::new("documentalist");
                let proof = entry.0.clone();

                let key = RevEntry::new("documental");
                let key = &key.entry();

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(&subentry.entry());
                _ = poetrie.ins(&entry.entry());
                _ = poetrie.ins(key);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(130, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn only_subentry_is_possible1() {
                let subentry = RevEntry::new("document");
                let entry = RevEntry::new("documental");
                let proof = entry.0.clone();

                let key = RevEntry::new("documentalist");
                let key = &key.entry();

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(&subentry.entry());
                _ = poetrie.ins(&entry.entry());
                _ = poetrie.ins(key);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(34, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn only_subentry_is_possible2() {
                let proof = String::from("m");
                let subentry = Entry(proof.as_str());

                let key = &Entry("anagram");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(&subentry);
                _ = poetrie.ins(key);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(34, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn only_subentry_is_possible3() {
                let proof = String::from("Xconundrum");
                let entry = Entry(proof.as_str());

                let key = &Entry("YXconundrum");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(&entry);
                _ = poetrie.ins(&key);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(34, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn only_subsuffix_is_possible1() {
                let subentry = RevEntry::new("document");
                let entry = RevEntry::new("documental");
                let proof = entry.0.clone();

                let key = RevEntry::new("documentalist");
                let key = &key.entry();

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(&subentry.entry());
                _ = poetrie.ins(&entry.entry());

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(40, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn only_subsuffix_is_possible2() {
                let proof = String::from("m");
                let entry = Entry(proof.as_str());

                let key = &Entry("conundrum");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(&entry);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(40, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn only_subsuffix_is_possible3() {
                let proof = String::from("Xconundrum");
                let entry = Entry(proof.as_str());

                let key = &Entry("YXconundrum");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(&entry);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(40, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn must_not_recourse_to_root_branching1() {
                let proof = String::from("hilum");
                let subentry = Entry(proof.as_str());
                let entry = Entry("claybank");

                let key = &Entry("haulm");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(&subentry);
                _ = poetrie.ins(&entry);
                _ = poetrie.ins(key);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(642, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn must_not_recourse_to_root_branching2() {
                let proof = String::from("hilum");
                let subentry = Entry(proof.as_str());
                let entry = Entry("claybank");

                let key = &Entry("haulm");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(&subentry);
                _ = poetrie.ins(&entry);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(132, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn key_partially_shared_suffix_1a() {
                let proof = String::from("lyrics");
                let entry = &Entry(proof.as_str());

                let key = &Entry("athletics");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(entry);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(132, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn key_partially_shared_suffix_1b() {
                let proof = String::from("lyrics");
                let entry = &Entry(proof.as_str());

                let key = &Entry("carboniferous");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(entry);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(132, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn key_partially_shared_suffix_2a() {
                let proof = String::from("lyrics");
                let entry = &Entry(proof.as_str());

                let key = &Entry("athletics");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(entry);
                _ = poetrie.ins(key);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(642, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn key_partially_shared_suffix_2b() {
                let proof = String::from("lyrics");
                let entry = &Entry(proof.as_str());

                let key = &Entry("carboniferous");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(entry);
                _ = poetrie.ins(key);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(642, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn key_partially_shared_suffix_3a() {
                let proof = String::from("X-lyrics");
                let entry = &Entry(proof.as_str());

                let key = &Entry("A-lyrics");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(entry);
                _ = poetrie.ins(key);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(642, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn key_partially_shared_suffix_3b() {
                let proof = String::from("X-lyrics");
                let entry = &Entry(proof.as_str());

                let key = &Entry("A-lyrics");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(entry);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(132, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn key_partially_shared_suffix_4a() {
                let proof_1 = String::from("lyrics");
                let entry_1 = &Entry(proof_1.as_str());

                let proof_2 = String::from("ethics");
                let entry_2 = &Entry(proof_2.as_str());

                let key = &Entry("athletics");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(entry_1);
                _ = poetrie.ins(entry_2);

                _ = poetrie.ins(key);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(642, b_code);

                let equal = Ok(proof_1) == find || Ok(proof_2) == find;

                assert_eq!(true, equal);
            }

            #[test]
            fn key_partially_shared_suffix_4b() {
                let proof_1 = String::from("lyrics");
                let entry_1 = &Entry(proof_1.as_str());

                let proof_2 = String::from("emphasis");
                let entry_2 = &Entry(proof_2.as_str());

                let key = &Entry("carboniferous");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(entry_1);
                _ = poetrie.ins(entry_2);

                _ = poetrie.ins(key);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(642, b_code);

                let equal = Ok(proof_1) == find || Ok(proof_2) == find;

                assert_eq!(true, equal);
            }

            #[test]
            fn prefer_suffix_entry_when_longer_share_1() {
                // branching entry
                let bra_ent = RevEntry::new("documentarian");
                let suf_ent = RevEntry::new("documental");
                let proof = suf_ent.0.clone();

                let key = RevEntry::new("documentalist");
                let key = &key.entry();

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(&suf_ent.entry());
                _ = poetrie.ins(&bra_ent.entry());

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(264, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn prefer_suffix_entry_when_longer_share_2() {
                // branching entry
                let bra_ent = RevEntry::new("documentarian");
                let suf_ent = RevEntry::new("documental");
                let proof = suf_ent.0.clone();

                let key = RevEntry::new("documentalist");
                let key = &key.entry();

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(&suf_ent.entry());
                _ = poetrie.ins(&bra_ent.entry());
                _ = poetrie.ins(key);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(258, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn prefer_branching_entry_when_at_least_same_share_1() {
                let bra_ent = RevEntry::new("documented");
                let proof = bra_ent.0.clone();

                // suffix entry
                let suf_ent = RevEntry::new("document");

                let key = RevEntry::new("documentalist");
                let key = &key.entry();

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(&suf_ent.entry());
                _ = poetrie.ins(&bra_ent.entry());

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(132, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn prefer_branching_entry_when_at_least_same_share_2() {
                let bra_ent = RevEntry::new("documented");
                let proof = bra_ent.0.clone();

                // suffix entry
                let suf_ent = RevEntry::new("document");

                let key = RevEntry::new("documentalist");
                let key = &key.entry();

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(&suf_ent.entry());
                _ = poetrie.ins(&bra_ent.entry());
                _ = poetrie.ins(key);

                let mut b_code = 0;
                let find = poetrie.find(key, &mut b_code);

                assert_eq!(642, b_code);
                assert_eq!(Ok(proof), find);
            }

            #[test]
            fn load() {
                let mut poetrie = Poetrie::new();

                let rev_entries = ["document", "documentalist"];
                let rev_entries = rev_entries.map(|x| RevEntry::new(x));
                let rev_entries = rev_entries.iter().map(|x| x.0.as_str());

                let entries = [
                    "aesthetics",
                    "statics",
                    "mechanics",
                    "athletics",
                    "physics",
                    "q",
                    "epically",
                ];
                for e in entries.iter().map(|x| *x).chain(rev_entries) {
                    _ = poetrie.ins(&Entry(e));
                }

                let key = Entry("musics");
                let proof = String::from("physics");
                assert(Ok(proof), 132, key, &poetrie);

                let key = Entry("athletics");
                let proof = String::from("aesthetics");
                assert(Ok(proof), 642, key, &poetrie);

                let key = Entry("aesthetics");
                let proof = String::from("athletics");
                assert(Ok(proof), 642, key, &poetrie);

                let key = Entry("epicalyx");
                assert(Err(FindErr::NoJointSuffix), 0, key, &poetrie);

                let key = RevEntry::new("documental");
                let proof = RevEntry::new("documentalist").0;
                assert(Ok(proof), 130, key.entry(), &poetrie);

                let key = RevEntry::new("documentalist");
                let proof = RevEntry::new("document").0;
                assert(Ok(proof), 34, key.entry(), &poetrie);

                let key = RevEntry::new("quadriceps");
                let proof = String::from("q");
                assert(Ok(proof), 40, key.entry(), &poetrie);

                let key = Entry("q");
                assert(Err(FindErr::OnlyKeyMatches), 18, key, &poetrie);

                let key = Entry("epically");
                assert(Err(FindErr::OnlyKeyMatches), 18, key, &poetrie);

                fn assert(
                    res: Result<String, FindErr>,
                    code: usize,
                    key: crate::Key,
                    poetrie: &Poetrie,
                ) {
                    let mut b_code = 0;
                    assert_eq!(res, poetrie.find(&key, &mut b_code));
                    assert_eq!(code, b_code);

                    poetrie.buf.get_mut().clear();
                }
            }
        }

        mod track {

            use super::super::rev_entry::RevEntry;
            use crate::{NULL, Poetrie, TraRes};

            #[test]
            fn tracing() {
                let mut poetrie = Poetrie::new();

                let keyword = "keyword";
                let entries = ["k", "key", keyword].map(|x| RevEntry::new(x));

                for e in entries.iter() {
                    _ = poetrie.ins(&e.entry());
                }

                let keyword_e = &entries[2].entry();
                _ = poetrie.track(keyword_e, true);

                let trace = &poetrie.btr;
                let proof = format!("{}{}", NULL, keyword);
                for (ix, c) in proof.chars().enumerate() {
                    let duo = trace[ix];
                    assert_eq!(c, duo.0, "{ix}");
                }

                for e in entries.iter() {
                    let (c, node) = trace[e.len()];
                    let node = unsafe { node.as_ref() }.unwrap();
                    assert_eq!(true, node.entry, "c: {c}, e: {}", **e);
                }

                poetrie.btr.get_mut().clear();
                _ = poetrie.track(keyword_e, false);
                assert_eq!(0, trace.len());
            }

            #[test]
            fn ok() {
                let entry = RevEntry::new("información meteorológica");
                let entry = &entry.entry();

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(entry);
                let res = poetrie.track(entry, false);

                assert_eq!(TraRes::Ok, res);
            }

            #[test]
            fn unknown_not_path() {
                let entry = RevEntry::new("wordbook");
                let bad_entry = RevEntry::new("wordbooks");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(&entry.entry());
                let res = poetrie.track(&bad_entry.entry(), false);
                assert_eq!(TraRes::UnknownForAbsentPathLinks, res);
            }

            #[test]
            fn unknown_not_path2() {
                let entry = RevEntry::new("wordbookz");
                let bad_entry = RevEntry::new("wordbooks");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(&entry.entry());
                let res = poetrie.track(&bad_entry.entry(), false);
                assert_eq!(TraRes::UnknownForAbsentPathNode, res);
            }

            #[test]
            fn unknown_not_entry() {
                let entry = RevEntry::new("wordbooks");
                let bad_entry = RevEntry::new("wordbook");

                let mut poetrie = Poetrie::new();
                _ = poetrie.ins(&entry.entry());

                let res = poetrie.track(&bad_entry.entry(), false);
                assert_eq!(TraRes::UnknownForNotEntry, res);
            }
        }

        #[test]
        fn ct() {
            let test = 3;
            let mut poetrie = Poetrie::new();
            assert_eq!(0, poetrie.ct());
            poetrie.cnt = test;
            assert_eq!(test, poetrie.ct());
        }

        mod ext {
            use crate::{Entry, Poetrie};

            #[test]
            fn basic_test() {
                let proof = vec![
                    String::from("aa"),
                    String::from("azbq"),
                    String::from("by"),
                    String::from("ybc"),
                    String::from("ybxr"),
                    String::from("ybxrqutmop"),
                    String::from("ybxrqutmopfvb"),
                    String::from("ybxrqutmoprfg"),
                    String::from("zazazazazabyyb"),
                ];

                let entries = proof.iter().map(|x| Entry(x.as_str()));

                let mut poetrie = Poetrie::new();
                for e in entries.clone() {
                    _ = poetrie.ins(&e);
                }

                let ext = poetrie.ext();
                assert_eq!(true, ext.is_some());
                let mut ext = ext.unwrap();

                assert_eq!(proof.len(), ext.len());

                ext.sort();
                assert_eq!(proof, ext);

                const CAP: usize = 5000;
                let cap = ext.capacity();

                assert_eq!(true, cap >= CAP);
                assert_eq!(true, cap < CAP * 2);

                for e in entries.clone() {
                    assert_eq!(true, poetrie.en(&e));
                }
            }

            #[test]
            fn empty_tree() {
                let mut poetrie = Poetrie::new();
                let ext = poetrie.ext();

                assert_eq!(None, ext);
            }
        }
    }

    mod node {

        use crate::{Links, Node};
        use std::ptr::addr_of;

        #[test]
        fn links() {
            let mut node = Node::empty();

            assert_eq!(false, node.links());
            node.links = Some(Links::new());
            assert!(node.links());
        }

        #[test]
        fn empty() {
            let node = Node::empty();

            assert_eq!(None, node.links);
            assert_eq!(false, node.entry);
        }

        #[test]
        fn to_mut_ptr() {
            let n = Node::empty();
            let n_add = addr_of!(n) as usize;
            assert_eq!(n_add, n.to_mut_ptr() as usize);
        }
    }
}

// cargo fmt && cargo test --release
