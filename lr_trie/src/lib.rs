//! To reduce memory demands of `LrTrie`, operations are not particularly optimal.
//! If alphabet used became wide enough, some rework using e.g. hashmap would be needed.

use std::ptr;
use std::string::String;
use std::vec::Vec;

type Links = Vec<Node>;
type Path<'a> = Vec<PathNode<'a>>;
type PathNode<'a> = (usize, &'a Node);

/// `KeyEntry` playing entry role.
pub type Entry<'a> = KeyEntry<'a>;
/// `KeyEntry` playing key role.
pub type Key<'a> = KeyEntry<'a>;

struct Node {
    c: char,
    supernode: *const Node,
    links: Option<Links>,
    lrref: *const Node,
    #[cfg(test)]
    id: usize,
}

const NULL: char = '\0';
const BASIC_WORD_LEN_GUESS: usize = 12;

impl Node {
    fn lrref(&self) -> bool {
        !self.lrref.is_null()
    }

    fn links(&self) -> bool {
        self.links.is_some()
    }

    fn empty() -> Self {
        let null_ptr = ptr::null();

        Node {
            c: NULL,
            supernode: null_ptr,
            links: None,
            lrref: null_ptr,
            #[cfg(test)]
            id: 0,
        }
    }

    fn new(c: char, supernode: *const Node) -> Self {
        Node {
            c,
            supernode,
            links: None,
            lrref: ptr::null(),
            #[cfg(test)]
            id: 0,
        }
    }
}

/// `&str` verified for working with `LrTrie`.
pub struct KeyEntry<'a>(&'a str, usize);

impl<'a> KeyEntry<'a> {
    /// Returns `None` for 0-len `key`.
    pub fn new(key: &'a str) -> Option<Self> {
        if key.len() == 0 {
            None
        } else {
            let len = key.chars().count();
            Some(Self(key, len))
        }
    }
}

impl<'a> std::ops::Deref for Key<'a> {
    type Target = str;

    /// Returns `&str` of key.
    fn deref(&self) -> &str {
        self.0
    }
}

/// Denotes desired target tree on respective operations.
#[derive(Clone, Debug, PartialEq)]
pub enum LeftRight {
    Left = 0,
    Right = 1,
}

fn path_from_key<'a>(key: &Key, mut node: &'a Node) -> Path<'a> {
    let mut path = Vec::with_capacity(key.1 + 1);

    path.push((usize::MAX, node));

    for c in key.chars() {
        if let Some(l) = &node.links {
            if let Some(ix) = index_of_c(l, c) {
                node = &l[ix];

                path.push((ix, node));
                continue;
            }
        }

        break;
    }

    path
}

fn path_from_entry<'a>(key_node: &'a Node) -> Path<'a> {
    let mut path = Vec::with_capacity(BASIC_WORD_LEN_GUESS);

    let mut n = unsafe { key_node.lrref.as_ref() }.unwrap();

    while let Some(supn) = unsafe { n.supernode.as_ref() } {
        let subn_ix = index_of_c(supn.links.as_ref().unwrap(), n.c).unwrap();

        path.push((subn_ix, n));

        n = supn;
    }

    path.push((usize::MAX, n));

    path
}

fn entry_path_node<'a>(path: &'a Path, key: &Key) -> Option<PathNode<'a>> {
    let exp_len = key.1 + 1;

    if path.len() == exp_len {
        let epn = path[key.1];
        if epn.1.lrref() {
            Some(epn)
        } else {
            None
        }
    } else {
        None
    }
}

fn index_of_c(links: &Links, c: char) -> Option<usize> {
    let links_len = links.len();
    let mut ix = 0;

    while ix < links_len {
        let n = &links[ix];
        if n.c == c {
            return Some(ix);
        }

        ix += 1;
    }

    None
}

fn mut_node<'a>(node: &Node) -> &'a mut Node {
    let ptr: *const Node = node;
    unsafe {
        core::mem::transmute::<*const Node, *mut Node>(ptr)
            .as_mut()
            .unwrap()
    }
}

/// Left-right trie is double-treed trie.
///
/// Allows for bi-directional mapping between two trees whereas each entry
/// has link to counterpart entry in opposite tree.
///
/// While each entry-entry pair is settled by nodes in respective tree,
/// each node carries extra reference to its supernode. Thus `LrTrie` is not memory effecient
/// unless nodes in each side are reasonably reclaimed.
///
/// All methods time complexity depends on subnodes count. Thus TC is Ο(alphabet-size).
pub struct LrTrie {
    left: Node,
    right: Node,
}

impl LrTrie {
    /// Ctor.
    pub fn new() -> Self {
        LrTrie {
            left: Node::empty(),
            right: Node::empty(),
        }
    }

    /// Inserts entries in respective trees making them pointing one to another.
    ///
    /// If entry already exists in respective tree, its current counterpart is removed.
    pub fn insert(&mut self, l_entry: &Entry, r_entry: &Entry) {
        // let not make exercises for exact reinsert since
        // it is supposed to be very rare if at all
        _ = self.delete_crux(l_entry, LeftRight::Left, true);
        _ = self.delete_crux(r_entry, LeftRight::Right, true);

        let l_en = Self::insert_crux(&mut self.left, l_entry);
        let r_en = Self::insert_crux(&mut self.right, r_entry);

        l_en.lrref = r_en as *const Node;
        r_en.lrref = l_en as *const Node;
    }

    fn insert_crux<'a>(mut node: &'a mut Node, e: &Entry) -> &'a mut Node {
        let e = e.0;

        let mut supernode: *const Node = node;
        for c in e.chars() {
            let links = node.links.get_or_insert_with(|| Links::new());

            let ix = if let Some(i) = index_of_c(links, c) {
                i
            } else {
                links.push(Node::new(c, supernode));
                links.len() - 1
            };

            node = &mut links[ix];
            supernode = node;
        }

        node
    }

    /// Seeks for member in other tree than is specified for key.
    ///
    /// Returns `None` if key is not associated with entry.
    pub fn member(&self, key: &Key, lr: LeftRight) -> Option<String> {
        let path = path_from_key(key, self.node(lr));
        let epn = entry_path_node(&path, key);

        if let Some(epn) = epn {
            let mut entry = Vec::with_capacity(BASIC_WORD_LEN_GUESS);

            let mut node = epn.1.lrref;

            loop {
                let n = unsafe { node.as_ref() }.unwrap();
                let supernode = n.supernode;

                if supernode == ptr::null() {
                    break;
                }

                entry.push(n.c);
                node = supernode;
            }

            Some(entry.iter().rev().collect::<String>())
        } else {
            None
        }
    }

    fn node(&self, lr: LeftRight) -> &Node {
        match lr {
            LeftRight::Left => &self.left,
            LeftRight::Right => &self.right,
        }
    }

    /// Deletes both key and its entry seeking key in specified tree.
    ///
    /// Returns `Err` when key is not associated with entry.
    pub fn delete(&mut self, key: &Key, lr: LeftRight) -> Result<(), ()> {
        self.delete_crux(key, lr, false)
    }

    fn delete_crux(&mut self, key: &Key, lr: LeftRight, preserve_ks: bool) -> Result<(), ()> {
        // key side path
        let ks_path = path_from_key(key, self.node(lr.clone()));
        let ks_epn = match entry_path_node(&ks_path, key) {
            Some(epn) => epn,
            _ => return Err(()),
        };

        // entry side path
        let es_path = path_from_entry(ks_epn.1);
        let es_epn = es_path[0];

        let deletion_data = [(es_epn, &es_path), (ks_epn, &ks_path)];
        for data_ix in 0..2 {
            let (epn, path) = deletion_data[data_ix];

            let epn_mut = mut_node(&epn.1); // sounds
            if epn_mut.links() {
                epn_mut.lrref = ptr::null();
                continue;
            }

            let (limit, mut ix) = if data_ix == 0 {
                (path.len() - 1, 1)
            } else {
                (0, path.len() - 2)
            };

            let mut subnode_ix = epn.0;
            loop {
                let (sn_ix, n) = path[ix];
                let n_mut = mut_node(n); // sounds

                let n_links = n_mut.links.as_mut().unwrap();
                _ = n_links.swap_remove(subnode_ix);

                if n_links.len() == 0 {
                    n_mut.links = None;
                } else {
                    break;
                }

                if n.lrref() {
                    break;
                }

                if ix == limit {
                    break;
                }

                if data_ix == 0 {
                    ix += 1;
                } else {
                    ix -= 1;
                }

                subnode_ix = sn_ix;
            }

            if preserve_ks {
                break;
            }
        }
        return Ok(());
    }
}

#[cfg(test)]
mod tests_of_units {

    use crate::{LeftRight, Links, LrTrie, Node};

    impl PartialEq for Node {
        fn eq(&self, other: &Self) -> bool {
            self.c == other.c
                && self.supernode == other.supernode
                && self.links == other.links
                && self.lrref == other.lrref
        }
    }

    use core::fmt::{Debug, Formatter};

    impl Debug for Node {
        fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
            let links = if self.links() { "Some" } else { "None" };
            let lrref = if self.lrref() { "Some" } else { "None" };
            let sn = if self.supernode.is_null() {
                "Null"
            } else {
                "Parent"
            };

            f.write_fmt(format_args!(
                "Node {{\n  c: {}\n  sn: {}\n  links: {}\n  lrref: {}\n}}",
                self.c, sn, links, lrref
            ))
        }
    }

    impl LrTrie {
        fn links(&self, lr: LeftRight) -> Option<&Links> {
            match lr {
                LeftRight::Left => self.left.links.as_ref(),
                LeftRight::Right => self.right.links.as_ref(),
            }
        }
    }

    impl LeftRight {
        fn invert(&self) -> Self {
            match self {
                LeftRight::Left => LeftRight::Right,
                LeftRight::Right => LeftRight::Left,
            }
        }
    }

    mod node {

        use crate::{Links, Node, NULL};
        use core::ptr;

        #[test]
        fn lrref() {
            let mut node = Node::empty();

            assert_eq!(false, node.lrref());
            node.lrref = &node;
            assert!(node.lrref());
        }

        #[test]
        fn links() {
            let mut node = Node::empty();

            assert_eq!(false, node.links());
            node.links = Some(Links::new());
            assert!(node.links());
        }

        #[test]
        fn empty() {
            let null_ptr = ptr::null();

            let node = Node::empty();

            assert_eq!(NULL, node.c);
            assert_eq!(null_ptr, node.supernode);
            assert_eq!(None, node.links);
            assert_eq!(null_ptr, node.lrref);
        }

        #[test]
        fn new() {
            let c = '🫀';
            let sn = Node::empty();

            let new = Node::new(c, &sn);

            assert_eq!(c, new.c);
            assert_eq!(&sn as *const Node, new.supernode);
            assert_eq!(None, new.links);
            assert_eq!(0, new.lrref as usize);
        }
    }

    mod keyentry {
        use crate::KeyEntry;

        mod new {
            use crate::KeyEntry;

            #[test]
            fn some() {
                const KEY: &str = "emoción";
                let key = KeyEntry::new(KEY);
                assert!(key.is_some());
                let key = key.unwrap();
                assert_eq!(KEY, key.0);
                assert_eq!(KEY.chars().count(), key.1);
            }

            #[test]
            fn none() {
                let key = KeyEntry::new("");
                assert!(key.is_none());
            }
        }

        use std::ops::Deref;

        #[test]
        fn deref() {
            const KEY: &str = "key";
            let key = KeyEntry::new(KEY).unwrap();
            assert_eq!(KEY, key.deref());
        }
    }

    mod path_from_key {

        use crate::{path_from_key as path_fn, Key, LrTrie, Node};

        #[test]
        fn path_from_key() {
            let mut trie = LrTrie::new();

            const KEYWORD: &str = "keyword";
            let keyword = Key::new(KEYWORD).unwrap();

            const KEYHOLE: &str = "keyhole";
            let keyhole = Key::new(KEYHOLE).unwrap();

            let words = ["key", KEYWORD, "keyboard", KEYHOLE];
            let kes = words.map(|x| Key::new(x).unwrap());

            for ke in &kes {
                trie.insert(ke, ke);
            }

            let l_root = &trie.left;

            for ke in &kes[..2] {
                let path = path_fn(&keyword, l_root);

                // path node
                let root_pn = &path[0];
                assert_eq!(usize::MAX, root_pn.0);

                let root: *const Node = root_pn.1;
                assert_eq!(l_root as *const Node, root);

                assert_eq!(KEYWORD.len() + 1, path.len());

                let mut ix = 1;
                for c in ke.0.chars() {
                    let pn = path[ix];
                    assert_eq!(0, pn.0);

                    let n = pn.1;
                    assert_eq!(c, n.c);
                    ix += 1;
                }

                assert!(path[ix - 1].1.lrref());
            }

            let path = path_fn(&keyhole, &trie.right);

            let h_node = &path[4];

            assert_eq!(2, h_node.0);
            assert_eq!('h', h_node.1.c);
        }

        #[test]
        fn no_branch() {
            let mut trie = LrTrie::new();

            let keyboard = Key::new("Keyboard").unwrap();
            let keyword = Key::new("Keyword").unwrap();

            trie.insert(&keyword, &keyword);

            let path = path_fn(&keyboard, &trie.left);

            const PROOF: &str = "Key";
            assert_eq!(PROOF.len() + 1, path.len());

            let mut ix = 1;
            for c in PROOF.chars() {
                let pn = path[ix];
                assert_eq!(c, pn.1.c);
                ix += 1;
            }
        }

        #[test]
        fn no_branches() {
            let node = Node::empty();

            let key = Key::new("key").unwrap();
            let path = path_fn(&key, &node);

            assert_eq!(1, path.len());
            let pn = &path[0];
            assert_eq!(usize::MAX, pn.0);
            assert_eq!(&node as *const Node, pn.1 as *const Node);
        }
    }

    use crate::{path_from_entry as path_fn, Entry, KeyEntry, NULL};

    #[test]
    fn path_from_entry() {
        const ENTRY: &str = "JourneyOfDecade";

        let key = KeyEntry::new("A").unwrap();
        let entry = KeyEntry::new(ENTRY).unwrap();
        let noise1 = Entry::new("JourneyOfYourLife").unwrap();
        let noise2 = Entry::new("JourneyOfOurLifes").unwrap();

        let mut trie = LrTrie::new();
        trie.insert(&noise1, &noise1);
        trie.insert(&noise2, &noise2);
        trie.insert(&key, &entry);

        let key_node = &trie.left.links.unwrap()[1];

        let path = path_fn(key_node);
        assert_eq!(path.len(), ENTRY.len() + 1);

        for (ix, c) in ENTRY.chars().rev().enumerate() {
            let pn = path[ix];

            assert_eq!(c, pn.1.c);

            let subn_ix = if c == 'D' {
                2
            } else if c == NULL {
                usize::MAX
            } else {
                0
            };

            assert_eq!(subn_ix, pn.0, "{c}");
        }
    }

    mod entry_path_node {
        extern crate std;

        use crate::{entry_path_node, Key, Node, Path};
        use std::iter::repeat_with;
        use std::ptr;
        use std::string::{String, ToString};
        use std::vec::Vec;

        fn replacement_key(n: usize) -> String {
            const REPLACEMENT: char = '\u{001A}';

            REPLACEMENT.to_string().repeat(n)
        }

        fn path_imitation(len: usize, node: &Node) -> Path {
            repeat_with(|| node)
                .enumerate()
                .take(len)
                .collect::<Vec<(usize, &Node)>>()
        }

        // longer key means it is not traced by path
        #[test]
        fn longer_key() {
            let empty = Node::empty();

            let path = path_imitation(4, &empty);
            let key = replacement_key(4);
            let key = Key::new(&key).unwrap();

            assert_eq!(None, entry_path_node(&path, &key));
        }

        #[test]
        fn not_entry() {
            let empty = Node::empty();

            let path = path_imitation(5, &empty);
            let key = replacement_key(4);
            let key = Key::new(&key).unwrap();

            assert_eq!(None, entry_path_node(&path, &key));
        }

        #[test]
        fn entry() {
            let empty = Node::empty();

            let mut en = Node::new('a', ptr::null());
            en.lrref = &empty;
            let en_ix = 4;

            let mut path = path_imitation(en_ix + 1, &empty);
            let key = replacement_key(4);
            let key = Key::new(&key).unwrap();

            path[en_ix].1 = &en;

            let epn = entry_path_node(&path, &key);
            assert!(epn.is_some());

            let epn = epn.unwrap();
            assert_eq!(en_ix, epn.0);

            let en = &epn.1;
            assert_eq!('a', en.c);
            assert_eq!(&empty as *const Node, en.lrref);
        }
    }

    mod index_of_c {

        use crate::{index_of_c, Links, Node};

        fn links(cs: &[char]) -> Links {
            cs.iter()
                .map(|x| Node::new(*x, 0 as *const Node))
                .collect::<Links>()
        }

        #[test]
        fn some() {
            let links = links(&['a', 'b', 'c']);

            let index = index_of_c(&links, 'c');
            assert!(index.is_some());
            assert_eq!(2, index.unwrap());
        }

        #[test]
        fn none() {
            let links = links(&['a', 'b', 'c']);

            let index = index_of_c(&links, 'd');
            assert!(index.is_none());
        }
    }

    use crate::mut_node as mut_node_fn;
    #[test]
    fn mut_node() {
        let node = Node::empty();

        let mut_node = mut_node_fn(&node);
        assert_eq!(&node as *const Node, mut_node as *const Node);
    }

    mod trie {

        use crate::{LeftRight, LrTrie, Node};

        #[test]
        fn new() {
            let trie = LrTrie::new();
            let empty = Node::empty();

            assert_eq!(empty, trie.left);
            assert_eq!(empty, trie.right);
        }

        mod insert {

            use crate::{Entry, Key, KeyEntry, LeftRight, Links, LrTrie, Node};

            fn last_node(links: &Links) -> &Node {
                let node = links.get(0);
                assert!(node.is_some());

                let mut node = node.unwrap();
                while let Some(l) = node.links.as_ref() {
                    let n = l.get(0);
                    assert!(n.is_some());

                    node = n.as_ref().unwrap();
                }

                node
            }

            fn insert(trie: &mut LrTrie, lke: &Entry, rke: &Entry) -> (*const Node, *const Node) {
                trie.insert(lke, rke);

                let l_links = &trie.left.links.as_ref().unwrap();
                let r_links = &trie.right.links.as_ref().unwrap();

                (last_node(l_links), last_node(r_links))
            }

            fn put_id(node: *const Node, val: usize) {
                let node = unsafe { core::mem::transmute::<*const Node, *mut Node>(node) };
                unsafe { node.as_mut() }.unwrap().id = val;
            }

            fn as_ref<'a>(node: *const Node) -> &'a Node {
                unsafe { node.as_ref() }.unwrap()
            }

            #[test]
            fn basic_test() {
                let left_ke = &KeyEntry::new("LEFT").unwrap();
                let right_ke = &KeyEntry::new("RIGHT").unwrap();

                let trie = &mut LrTrie::new();
                trie.insert(left_ke, right_ke);

                let left = verify(trie, left_ke, LeftRight::Left, right_ke);
                let right = verify(trie, right_ke, LeftRight::Right, left_ke);

                assert_eq!(left.lrref, right as *const Node);
                assert_eq!(right.lrref, left as *const Node);

                fn verify<'a>(trie: &'a LrTrie, key: &Key, lr: LeftRight, e: &Entry) -> &'a Node {
                    let member = trie.member(key, lr.clone());
                    assert!(member.is_some());
                    assert_eq!(e.0, &member.unwrap());

                    last_node(trie.links(lr).unwrap())
                }
            }

            #[test]
            fn reinsert_same() {
                let left_ke = &KeyEntry::new("LEFT").unwrap();
                let right_ke = &KeyEntry::new("RIGHT").unwrap();

                let trie = &mut LrTrie::new();

                let (lln_a_ptr, rln_a_ptr) = insert(trie, left_ke, right_ke);

                put_id(lln_a_ptr, 1);
                put_id(rln_a_ptr, 2);

                let (lln_b_ptr, rln_b_ptr) = insert(trie, left_ke, right_ke);

                let lln_b_ref = as_ref(lln_b_ptr);
                let rln_b_ref = as_ref(rln_b_ptr);

                assert_eq!(1, lln_b_ref.id); // left (key side) preserved
                assert_ne!(2, rln_b_ref.id); // right (entry side) removed
                assert_eq!(0, rln_b_ref.id); // right (entry side) removed

                verify(trie, left_ke, LeftRight::Left, right_ke);
                verify(trie, right_ke, LeftRight::Right, left_ke);

                fn verify(trie: &LrTrie, key: &Key, lr: LeftRight, e: &Entry) {
                    let member = trie.member(key, lr);
                    assert!(member.is_some());
                    assert_eq!(e.0, member.unwrap());
                }
            }

            #[test]
            fn reinsert_different() {
                let one = &KeyEntry::new("ONE").unwrap();
                let another = &KeyEntry::new("ANOTHER").unwrap();
                let replacement = &KeyEntry::new("REPLACEMENT").unwrap();

                for lr in [LeftRight::Left, LeftRight::Right] {
                    let trie = &mut LrTrie::new();

                    let (lln_a_ptr, rln_a_ptr) = insert(trie, one, another);

                    put_id(lln_a_ptr, 97);
                    put_id(rln_a_ptr, 98);

                    let (lln_b_ptr, rln_b_ptr) = if lr == LeftRight::Left {
                        insert(trie, replacement, another)
                    } else {
                        insert(trie, one, replacement)
                    };

                    let (lln_b_ref, rln_b_ref) = (as_ref(lln_b_ptr), as_ref(rln_b_ptr));

                    let (kept, removed) = if lr == LeftRight::Left {
                        assert_eq!(0, lln_b_ref.id);
                        assert_eq!(98, rln_b_ref.id);
                        (another, one)
                    } else {
                        assert_eq!(97, lln_b_ref.id);
                        assert_eq!(0, rln_b_ref.id);
                        (one, another)
                    };

                    assert!(trie.member(replacement, lr.clone()).is_some());
                    assert!(trie.member(kept, lr.clone().invert()).is_some());
                    assert!(trie.member(removed, lr).is_none());
                }
            }
        }

        mod insert_crux {
            use crate::{path_from_key, Entry, KeyEntry, LrTrie, Node};

            #[test]
            fn basic_test() {
                let mut root = Node::empty();

                const ENTRY: &str = "lr_links_inserT";
                let limit = ENTRY.len() - 1;

                let entry = Entry::new(ENTRY).unwrap();
                let node = LrTrie::insert_crux(&mut root, &entry);

                assert_eq!('T', node.c);
                assert_eq!(None, node.links);

                assert!(root.links.is_some());

                let mut links = root.links.as_ref().unwrap();
                let mut supernode: *const Node = &root;
                for (ix, c) in ENTRY.chars().enumerate() {
                    let node = links.get(0);

                    assert!(node.is_some());
                    let node = node.unwrap();

                    assert_eq!(c, node.c);
                    assert_eq!(supernode, node.supernode);
                    supernode = node;

                    if ix < limit {
                        let temp = &node.links;
                        assert!(temp.is_some());
                        links = temp.as_ref().unwrap();
                    } else {
                        assert!(&node.links.is_none());
                    }
                }
            }

            #[test]
            fn existing_path_insert() {
                let mut root = Node::empty();

                const OLD: &str = "touchstone";
                const NEW: &str = "touch";

                let old = KeyEntry::new(OLD).unwrap();
                let new = KeyEntry::new(NEW).unwrap();

                _ = LrTrie::insert_crux(&mut root, &old);
                _ = LrTrie::insert_crux(&mut root, &new);

                let old_path = path_from_key(&old, &root);
                let new_path = path_from_key(&new, &root);

                assert_eq!(OLD.len() + 1, old_path.len());
                assert_eq!(new_path, old_path[..NEW.len() + 1]);
            }
        }

        mod member {

            use crate::{Entry, Key, KeyEntry, LeftRight, LrTrie};

            #[test]
            fn member() {
                let left_ke = KeyEntry::new("LEFT").unwrap();
                let right_ke = KeyEntry::new("RIGHT").unwrap();

                let mut trie = LrTrie::new();
                trie.insert(&left_ke, &right_ke);

                verify(&left_ke, LeftRight::Left, &right_ke, &trie);
                verify(&right_ke, LeftRight::Right, &left_ke, &trie);

                fn verify(key: &Key, lr: LeftRight, e: &Entry, trie: &LrTrie) {
                    let entry = trie.member(key, lr);
                    assert!(entry.is_some());
                    assert_eq!(e.0, &entry.unwrap());
                }
            }

            #[test]
            fn not_member() {
                let keyword = KeyEntry::new("Keyword").unwrap();

                let mut trie = LrTrie::new();
                trie.insert(&keyword, &keyword);

                for lr in [LeftRight::Left, LeftRight::Right] {
                    for key in ["Key", "Opener"] {
                        let key = KeyEntry::new(key).unwrap();

                        let member = trie.member(&key, lr.clone());
                        assert!(member.is_none());
                    }
                }
            }
        }

        #[test]
        fn node() {
            let trie = LrTrie::new();

            let left: *const Node = &trie.left;
            let right: *const Node = &trie.right;

            assert_eq!(left, trie.node(LeftRight::Left));
            assert_eq!(right, trie.node(LeftRight::Right));
        }

        /// Node in path to entry being deleted
        /// cannot be deleted if and only if participates
        /// in path to another entry. Path len varies 0…m.
        mod delete {

            use crate::{path_from_key, Key, KeyEntry, LeftRight, LrTrie};

            #[test]
            fn not_member() {
                let keyword = KeyEntry::new("Keyword").unwrap();

                let mut trie = LrTrie::new();
                trie.insert(&keyword, &keyword);

                for lr in [LeftRight::Left, LeftRight::Right] {
                    for bad_key in ["Key", "Opener"] {
                        let bad_key = KeyEntry::new(bad_key).unwrap();

                        let err = trie.delete(&bad_key, lr.clone());
                        assert!(err.is_err());

                        assert!(trie.member(&keyword, lr.clone()).is_some());
                    }
                }
            }

            #[test]
            fn inner_entry() {
                let mut trie = LrTrie::new();

                let outer = KeyEntry::new("Keyword").unwrap();
                trie.insert(&outer, &outer);

                for lr in [LeftRight::Left, LeftRight::Right] {
                    let inner = KeyEntry::new("Key").unwrap();
                    trie.insert(&inner, &inner);

                    assert!(trie.delete(&inner, lr).is_ok());
                    assert!(trie.member(&inner, LeftRight::Left).is_none());
                    assert!(trie.member(&inner, LeftRight::Right).is_none());
                    assert!(trie.member(&outer, LeftRight::Left).is_some());
                    assert!(trie.member(&outer, LeftRight::Right).is_some());
                }
            }

            #[test]
            fn branching_node() {
                let keyword = KeyEntry::new("Keyword").unwrap();
                let keyboard = KeyEntry::new("Keyboard").unwrap();
                let keypad = KeyEntry::new("Keypad").unwrap();
                let key = Key::new("Key").unwrap();

                for lr in [LeftRight::Left, LeftRight::Right] {
                    let mut trie = LrTrie::new();
                    trie.insert(&keyword, &keyword);
                    trie.insert(&keyboard, &keyboard);
                    trie.insert(&keypad, &keypad);

                    assert!(trie.delete(&keyboard, lr).is_ok());

                    for lr in [LeftRight::Left, LeftRight::Right] {
                        assert!(trie.member(&keyboard, lr.clone()).is_none());
                        assert!(trie.member(&keyword, lr.clone()).is_some());
                        assert!(trie.member(&keypad, lr.clone()).is_some());

                        let path = path_from_key(&key, trie.node(lr));
                        let node = path[key.len()].1;
                        let links = node.links.as_ref().unwrap();
                        assert_eq!(2, links.len());
                        let filtered = links.iter().filter(|x| x.c == 'w' || x.c == 'p').count();
                        assert_eq!(2, filtered);
                    }
                }
            }

            #[test]
            fn links_removal() {
                let keyword = KeyEntry::new("Keyword").unwrap();
                let mut trie = LrTrie::new();

                for lr in [LeftRight::Left, LeftRight::Right] {
                    trie.insert(&keyword, &keyword);

                    assert!(trie.delete(&keyword, lr.clone()).is_ok());
                    assert!(trie.member(&keyword, lr.clone()).is_none());
                    assert!(trie.member(&keyword, lr.invert()).is_none());

                    assert!(trie.links(LeftRight::Left).is_none());
                    assert!(trie.links(LeftRight::Right).is_none());
                }
            }

            #[test]
            fn node_composing_path() {
                let dissimilar = KeyEntry::new("Dissimilar").unwrap();
                let keyword = KeyEntry::new("Keyword").unwrap();

                for lr in [LeftRight::Left, LeftRight::Right] {
                    let mut trie = LrTrie::new();

                    trie.insert(&dissimilar, &dissimilar);
                    trie.insert(&keyword, &keyword);

                    assert!(trie.delete(&keyword, lr.clone()).is_ok());
                    assert!(trie.member(&keyword, lr.clone()).is_none());
                    assert!(trie.member(&dissimilar, lr).is_some());
                }
            }

            #[test]
            fn node_being_entry() {
                let keyword = KeyEntry::new("Keyword").unwrap();
                let k = KeyEntry::new("K").unwrap();

                let mut trie = LrTrie::new();
                trie.insert(&k, &k);

                for lr in [LeftRight::Left, LeftRight::Right] {
                    trie.insert(&keyword, &keyword);

                    assert!(trie.delete(&keyword, lr.clone()).is_ok());
                    assert!(trie.member(&keyword, lr.clone()).is_none());
                    assert!(trie.member(&k, lr.clone()).is_some());

                    let links = trie.links(lr);
                    let k = &links.unwrap()[0];
                    assert_eq!(false, k.links());
                }
            }
        }
    }
}
