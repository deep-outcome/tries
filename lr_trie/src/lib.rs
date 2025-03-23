//! To reduce memory demands of `LrTrie`, operations are not particularly optimal.
//! If alphabet used became wide enough, some rework using e.g. hashmap would be needed.

use std::ptr;
use std::string::String;
use std::vec::Vec;

mod tra;
use tra::{tsdv, TraStrain};

mod uc;
use uc::UC;

type Links = Vec<Box<Node>>;
type NodeTrace = Vec<PathNode>;
type EntryTrace = Vec<char>;

#[derive(Clone, PartialEq, Debug)]
struct PathNode(usize, *mut Node);

impl PathNode {
    fn n_mut<'a>(&self) -> &'a mut Node {
        Node::as_mut(self.1)
    }
}

/// `KeyEntry` playing entry role.
pub type Entry<'a> = KeyEntry<'a>;
/// `KeyEntry` playing key role.
pub type Key<'a> = KeyEntry<'a>;

#[cfg_attr(test, derive(Clone))]
struct Node {
    c: char,
    supernode: *const Node,
    links: Option<Links>,
    lrref: *const Node,
    #[cfg(test)]
    id: usize,
}

const NULL_CHAR: char = '\0';
const NULL_NODE: *const Node = ptr::null();

impl Node {
    fn lrref(&self) -> bool {
        self.lrref != NULL_NODE
    }

    const fn links(&self) -> bool {
        self.links.is_some()
    }

    const fn empty() -> Self {
        Node {
            c: NULL_CHAR,
            supernode: NULL_NODE,
            links: None,
            lrref: NULL_NODE,
            #[cfg(test)]
            id: 0,
        }
    }

    const fn new(c: char, supernode: *const Node) -> Self {
        Node {
            c,
            supernode,
            links: None,
            lrref: NULL_NODE,
            #[cfg(test)]
            id: 0,
        }
    }

    fn empty_boxed() -> Box<Self> {
        Box::new(Self::empty())
    }

    fn new_boxed(c: char, supernode: *const Node) -> Box<Self> {
        Box::new(Self::new(c, supernode))
    }

    fn as_mut<'a>(n: *mut Self) -> &'a mut Self {
        unsafe { n.as_mut().unwrap_unchecked() }
    }

    fn as_ref<'a>(n: *const Self) -> &'a Self {
        unsafe { n.as_ref().unwrap_unchecked() }
    }

    const fn to_mut_ptr(&self) -> *mut Self {
        (self as *const Self).cast_mut()
    }
}

/// `&str` verified for working with `LrTrie`.
pub struct KeyEntry<'a>(&'a str);

impl<'a> KeyEntry<'a> {
    /// Returns `None` for 0-len `key`.
    pub const fn new(key: &'a str) -> Option<Self> {
        if key.len() == 0 {
            None
        } else {
            Some(Self(key))
        }
    }
}

impl<'a> std::ops::Deref for KeyEntry<'a> {
    type Target = str;

    /// Returns `&str` of key.
    fn deref(&self) -> &str {
        self.0
    }
}

/// Denotes desired target tree on respective operations.
#[cfg_attr(test, derive(Clone, Debug, PartialEq))]
pub enum LeftRight {
    Left = 0,
    Right = 1,
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

const fn cl_lrref(keyentry_n: &mut Node) -> bool {
    if keyentry_n.links() {
        keyentry_n.lrref = NULL_NODE;
        true
    } else {
        false
    }
}

fn delete_subnode(n: &mut Node, subnode_ix: usize) -> bool {
    let n_links = n.links.as_mut().unwrap();
    _ = n_links.swap_remove(subnode_ix);

    if n_links.len() == 0 {
        n.links = None;
    } else {
        return true;
    }

    if n.lrref() {
        return true;
    }

    return false;
}

fn delete_key_side<'a>(path: &NodeTrace) {
    let mut path = path.iter();
    let epn = path.next_back();
    let epn = unsafe { epn.unwrap_unchecked() };
    let n = epn.n_mut();

    if cl_lrref(n) {
        return;
    }

    let mut sub_n_ix = epn.0;
    while let Some(PathNode(n_ix, n)) = path.next_back() {
        if delete_subnode(Node::as_mut(*n), sub_n_ix) {
            break;
        }

        sub_n_ix = *n_ix;
    }
}

fn delete_entry_side(key_side_entry_n: &Node) {
    let lrref = key_side_entry_n.lrref.cast_mut();
    let node = Node::as_mut(lrref);

    if cl_lrref(node) {
        return;
    }

    const NULL_MUT: *mut Node = ptr::null_mut();
    let mut node: &mut Node = node;
    loop {
        let super_n = node.supernode.cast_mut();
        if super_n == NULL_MUT {
            break;
        }

        let super_n = Node::as_mut(super_n);
        let sn_links = unsafe { super_n.links.as_ref().unwrap_unchecked() };
        let n_ix = unsafe { index_of_c(sn_links, node.c).unwrap_unchecked() };

        if delete_subnode(super_n, n_ix) {
            break;
        }

        node = super_n;
    }
}

fn set_cap<T>(buf: &UC<Vec<T>>, approx_cap: usize) -> usize {
    let buf = buf.get_mut();
    let cp = buf.capacity();

    if cp < approx_cap {
        buf.reserve(approx_cap);
    } else if cp > approx_cap {
        *buf = Vec::with_capacity(approx_cap);
    }

    buf.capacity()
}

fn ext(l: &Links, k_buf: &mut String, e_buf: &mut Vec<char>, o: &mut Vec<(String, String)>) {
    for n in l {
        k_buf.push(n.c);

        let lrref = n.lrref;
        if lrref != NULL_NODE {
            let k = k_buf.clone();
            let e = construct_e(lrref, e_buf);
            o.push((k, e));
        }

        if let Some(l) = n.links.as_ref() {
            ext(l, k_buf, e_buf, o);
        }

        _ = k_buf.pop();
    }
}

fn construct_e(mut node: *const Node, e_buf: &mut Vec<char>) -> String {
    loop {
        let n = Node::as_ref(node);
        let super_n = n.supernode;

        if super_n == NULL_NODE {
            break;
        }

        e_buf.push(n.c);
        node = super_n;
    }

    let ret = e_buf.iter().rev().collect::<String>();
    e_buf.clear();
    ret
}

/// Denotes desired buffer on respective operations.
#[derive(Clone, PartialEq, Debug)]
pub enum Buffer {
    /// Delete method buffer denotation.
    Delete = 0,
    /// Member method buffer denotation.
    Member = 1,
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
/// All methods asymptotical computational time complexity depends on subnodes count,
/// i.e. Ο(alphabet-size). For small alphabets applies rather Ο(key-length). `member` method
/// is more requiring because of entry construction.
///
/// Node occurs per every `char` as defined by Rust lang.
#[cfg_attr(test, derive(PartialEq, Debug))]
pub struct LrTrie {
    left: Node,
    right: Node,
    // backtracing buffer
    trace: UC<NodeTrace>,
    entry: UC<EntryTrace>,
    count: usize,
}

#[cfg_attr(test, derive(PartialEq, Debug))]
enum TraRes<'a> {
    Ok,
    OkRef(&'a Node),
    UnknownForNotEntry,
    UnknownForAbsentPathLinks,
    UnknownForAbsentPathNode,
}

impl LrTrie {
    /// Ctor.
    pub const fn new() -> Self {
        LrTrie {
            left: Node::empty(),
            right: Node::empty(),
            trace: UC::new(Vec::new()),
            entry: UC::new(Vec::new()),
            count: 0,
        }
    }

    /// Inserts entries in respective trees making them pointing one to another.
    ///
    /// If entry already exists in respective tree, its current counterpart is removed.
    pub fn insert(&mut self, l_entry: &Entry, r_entry: &Entry) {
        // let not make exercises for exact reinsert since
        // it is supposed to be very rare, if at all

        let mut cntr = 0;
        if self.delete_crux(l_entry, LeftRight::Left, false).is_ok() {
            cntr += 1;
        }
        if self.delete_crux(r_entry, LeftRight::Right, false).is_ok() {
            cntr += 1;
        }

        let l_en = Self::insert_crux(&mut self.left, l_entry);
        let r_en = Self::insert_crux(&mut self.right, r_entry);

        l_en.lrref = r_en as *const Node;
        r_en.lrref = l_en as *const Node;

        let count = self.count;
        self.count = match cntr {
            0 => count + 1,
            1 => return,
            2 => count - 1,
            _ => panic!("Impossible value."),
        }
    }

    fn insert_crux<'a>(mut supernode: &'a mut Node, e: &Entry) -> &'a mut Node {
        let e = e.0;

        let mut swap = Node::empty_boxed();
        let mut sn_ptr: *const Node = supernode;
        for c in e.chars() {
            let links = supernode.links.get_or_insert_with(|| Links::new());

            let ix = if let Some(i) = index_of_c(links, c) {
                i
            } else {
                let boxed = Node::new_boxed(c, sn_ptr);
                links.push(boxed);
                links.len() - 1
            };

            let node = &mut links[ix];

            // Can be made coherent after
            // https://github.com/rust-lang/rust/issues/129090.
            std::mem::swap(&mut swap, node);
            let n_raw = Box::into_raw(swap);
            swap = unsafe { Box::from_raw(n_raw) };
            std::mem::swap(&mut swap, node);

            supernode = node;

            sn_ptr = n_raw;
        }

        supernode
    }

    fn track(&self, key: &Key, lr: LeftRight, ts: TraStrain) -> TraRes {
        let root = self.root(lr);
        let trace = self.trace.get_mut();

        let tracing = TraStrain::has(ts.clone(), tsdv::TRA);
        if tracing {
            trace.push(PathNode(usize::MAX, root.to_mut_ptr()));
        }

        let mut key = key.chars();
        let mut node = Node::as_ref(root);
        while let Some(c) = key.next() {
            if let Some(l) = &node.links {
                if let Some(ix) = index_of_c(l, c) {
                    node = &l[ix];
                    if tracing {
                        trace.push(PathNode(ix, node.to_mut_ptr()));
                    }

                    continue;
                }
                return TraRes::UnknownForAbsentPathNode;
            }
            return TraRes::UnknownForAbsentPathLinks;
        }

        if node.lrref() {
            match ts {
                x if TraStrain::has(x.clone(), tsdv::REF) => TraRes::OkRef(node),
                x if TraStrain::has(x.clone(), tsdv::EMP) => TraRes::Ok,
                _ => panic!("Unsupported result scenario."),
            }
        } else {
            TraRes::UnknownForNotEntry
        }
    }

    /// Seeks for member in other tree than is specified for key.
    ///
    /// Returns `None` if key is not associated with entry.
    pub fn member(&self, key: &Key, lr: LeftRight) -> Option<String> {
        let res = self.track(key, lr, TraStrain::NonRef);

        if let TraRes::OkRef(en) = res {
            let entry = self.entry.get_mut();

            let ret = construct_e(en.lrref, entry);
            Some(ret)
        } else {
            None
        }
    }

    const fn root(&self, lr: LeftRight) -> &Node {
        match lr {
            LeftRight::Left => &self.left,
            LeftRight::Right => &self.right,
        }
    }

    /// Deletes both key and its entry seeking key in specified tree.
    ///
    /// Returns `Err` when key is not associated with entry.
    pub fn delete(&mut self, key: &Key, lr: LeftRight) -> Result<(), ()> {
        let res = self.delete_crux(key, lr, true);
        self.trace.get_mut().clear();

        if res.is_ok() {
            self.count -= 1;
        }

        res
    }

    fn delete_crux(&mut self, key: &Key, lr: LeftRight, delete_ks: bool) -> Result<(), ()> {
        let ts = if delete_ks {
            TraStrain::TraRef
        } else {
            TraStrain::NonRef
        };

        if let TraRes::OkRef(en) = self.track(key, lr, ts) {
            delete_entry_side(en);

            if delete_ks {
                delete_key_side(&*self.trace)
            }

            Ok(())
        } else {
            Err(())
        }
    }

    /// `LrTrie` uses internal buffers, to avoid excessive allocations and copying, which grow
    /// over time due:
    /// - either backtracing when `delete`-ing, which backtraces whole path from entry
    /// node to root node
    /// - or entry constructing in `member`, when traversing back to root
    ///
    /// Use this method to shrink or extend buffer to fit actual program needs. Neither shrinking nor extending
    /// is guaranteed to be exact. See `Vec::with_capacity()` and `Vec::reserve()`. For optimal
    /// performance, set `approx_cap` to, at least, `key.chars().count()`.
    ///
    /// Some high value is sufficient anyway. Since buffer continuous
    /// usage, its capacity will likely expand at some point in time to size sufficient to all keys.
    ///
    /// Returns actual buffer capacity.
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
    pub fn put_buf_cap(&mut self, approx_cap: usize, buf: Buffer) -> usize {
        if buf == Buffer::Delete {
            set_cap(&self.trace, approx_cap)
        } else {
            #[cfg(test)]
            assert_eq!(Buffer::Member, buf);

            set_cap(&self.entry, approx_cap)
        }
    }

    /// Acquires corresponding buffer capacity.
    ///
    /// Check with `fn put_buf_cap` for details.
    pub fn aq_buf_cap(&self, buf: Buffer) -> usize {
        if buf == Buffer::Delete {
            self.trace.capacity()
        } else {
            #[cfg(test)]
            assert_eq!(Buffer::Member, buf);

            self.entry.capacity()
        }
    }

    /// Clears both trees leaving `LrTrie` instance blank.
    ///
    /// Keeps capacity of all of internal buffers intact. Check with `put_buf_cap` for details.
    pub fn clear(&mut self) {
        self.left = Node::empty();
        self.right = Node::empty();
        self.count = 0;
    }

    /// Returns actual count of entry-entry pairs.
    pub const fn count(&self) -> usize {
        self.count
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

    mod node_test_imp {
        use crate::Node;

        #[test]
        fn eq() {
            let sn = Node::empty();
            let mut n1 = Node::new('x', &sn);
            let links = vec![Node::new_boxed('y', &sn)];
            n1.links = Some(links);
            n1.lrref = &sn;

            let n2 = n1.clone();

            assert_eq!(true, n1.eq(&n2));
        }
    }

    use std::fmt::{Debug, Formatter};

    impl Debug for Node {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
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

    use crate::NodeTrace;
    impl LrTrie {
        fn links(&self, lr: LeftRight) -> Option<&Links> {
            match lr {
                LeftRight::Left => self.left.links.as_ref(),
                LeftRight::Right => self.right.links.as_ref(),
            }
        }

        fn cc_trace(&mut self) -> NodeTrace {
            let trace = self.trace.get_mut();
            let clone = trace.clone();
            trace.clear();
            clone
        }
    }

    mod lrtrie_test_impl {
        use std::ptr::NonNull;

        use crate::{LeftRight, Links, LrTrie, Node, PathNode};

        #[test]
        fn links() {
            let mut trie = LrTrie::new();
            let l_proof: *const Links = trie.left.links.get_or_insert(Links::new());
            let r_proof: *const Links = trie.right.links.get_or_insert(Links::new());

            let l_test: *const Links = trie.links(LeftRight::Left).unwrap();
            let r_test: *const Links = trie.links(LeftRight::Right).unwrap();

            assert_eq!(l_proof, l_test);
            assert_eq!(r_proof, r_test);
        }

        #[test]
        fn cc_trace() {
            let n1 = NonNull::<Node>::dangling().as_ptr();
            let n2 = NonNull::<Node>::dangling().as_ptr();

            let mut trie = LrTrie::new();
            let trace = trie.trace.get_mut();
            trace.push(PathNode(usize::MIN, n1));
            trace.push(PathNode(usize::MAX, n2));

            let proof = trace.clone();
            let test = trie.cc_trace();

            assert_eq!(proof, test);
            assert_eq!(0, trie.trace.len());
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

    mod leftright_test_impl {
        use crate::LeftRight;

        #[test]
        fn invert() {
            assert_eq!(LeftRight::Left, LeftRight::Right.invert());
            assert_eq!(LeftRight::Right, LeftRight::Left.invert());
        }
    }

    use crate::PathNode;
    impl PathNode {
        fn n_ref<'a>(&self) -> &'a Node {
            Node::as_ref(self.1)
        }
    }

    mod pathnode_test_impl {
        use crate::{Node, PathNode};

        #[test]
        fn n_ref() {
            let mut n = Node::empty();
            let pn = PathNode(0, &mut n);
            assert_eq!(
                &n as *const Node as usize,
                pn.n_ref() as *const Node as usize
            );
        }
    }

    mod pathnode {
        use crate::{Node, PathNode};

        #[test]
        fn n_mut() {
            let n = &mut Node::empty();
            let pn = PathNode(0, n);
            assert_eq!(
                n as *const Node as usize,
                pn.n_mut() as *const Node as usize
            );
        }
    }

    mod node {

        use crate::{Links, Node, NULL_CHAR};
        use std::ptr;

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

            assert_eq!(NULL_CHAR, node.c);
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

        #[test]
        fn as_mut() {
            let n = &mut Node::empty() as *mut Node;
            assert_eq!(n as usize, Node::as_mut(n) as *const Node as usize);
        }

        #[test]
        fn as_ref() {
            let n = &Node::empty() as *const Node;
            assert_eq!(n as usize, Node::as_ref(n) as *const Node as usize);
        }

        #[test]
        fn to_mut_ptr() {
            let n = Node::empty();
            let n_add = &n as *const Node as usize;
            assert_eq!(n_add, n.to_mut_ptr() as usize);
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
            let key = KeyEntry(KEY);
            assert_eq!(KEY, key.deref());
        }
    }

    mod index_of_c {

        use crate::{index_of_c, Links, Node};

        fn links(cs: &[char]) -> Links {
            cs.iter()
                .map(|x| Node::new_boxed(*x, 0 as *const Node))
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

    mod cl_lrref {
        use crate::{cl_lrref, Links, Node};
        use std::ptr;

        #[test]
        fn has_to() {
            let mut node = Node::empty();
            node.lrref = &node;
            node.links = Some(Links::new());

            assert_eq!(true, cl_lrref(&mut node));
            assert_eq!(ptr::null(), node.lrref);
        }

        #[test]
        fn has_not_to() {
            let mut node = Node::empty();
            node.lrref = &node;

            assert_eq!(false, cl_lrref(&mut node));
            assert_eq!(&node as *const Node, node.lrref);
        }
    }

    mod delete_subnode {
        use crate::{delete_subnode, Links, Node};
        use std::{ops::Deref, vec};

        // deletion continues when and only when
        // node does not participates in path to another
        // node, where path length is allowed to be 0
        #[test]
        fn deletion_continues() {
            let mut node = Node::empty();
            node.links = Some(vec![Node::empty_boxed()]);

            assert_eq!(false, delete_subnode(&mut node, 0));
            assert_eq!(None, node.links);
        }

        // when node holds some links after removing subnode in
        // question, it participates in path to another node
        #[test]
        fn node_with_links() {
            let mut node = Node::empty();

            #[rustfmt::skip]
            let links = vec![                
            Node::empty_boxed(),
            Node::new_boxed('a', 0 as *const Node),
            Node::new_boxed('b', 0 as *const Node),
            Node::new_boxed('c', 0 as *const Node),
            ];

            node.links = Some(links);
            assert_eq!(true, delete_subnode(&mut node, 1));

            let links = node.links.as_ref().unwrap();
            assert_eq!(3, links.len());
            assert_eq!(&Node::empty(), links[0].deref());
            assert_eq!('c', links[1].c);
            assert_eq!('b', links[2].c);
        }

        // key node has reference to entry node
        // so it participates in 0-len path to
        // another node
        #[test]
        fn key_node() {
            let mut node = Node::empty();

            node.links = Some(vec![Node::empty_boxed()]);
            node.lrref = &node;

            assert_eq!(true, delete_subnode(&mut node, 0));
            assert_eq!(None, node.links);
        }

        #[test]
        #[should_panic(expected = "swap_remove index (is 0) should be < len (is 0)")]
        fn index_out_of_bounds() {
            let mut node = Node::empty();
            node.links = Some(Links::new());
            delete_subnode(&mut node, 0);
        }
    }

    mod delete_key_side {
        use crate::{delete_key_side, Links, Node, PathNode};
        use std::{ops::DerefMut, ptr};

        #[test]
        fn keynode_with_links() {
            let mut n = Node::empty();
            n.lrref = &n;
            n.links = Some(Links::new());

            #[rustfmt::skip]
            let path = vec![
                PathNode(usize::MAX, &mut n),
                PathNode(usize::MAX, &mut n)
            ];

            delete_key_side(&path);

            assert_eq!(ptr::null(), n.lrref);
        }

        #[test]
        fn node_with_links() {
            let mut empty_n = Node::empty();

            let mut n = Node::empty();
            n.links = Some(vec![Node::empty_boxed(), Node::empty_boxed()]);

            #[rustfmt::skip]
            let path = vec![
                PathNode(usize::MAX, &mut empty_n),
                PathNode(usize::MAX, &mut n),
                PathNode(1, &mut empty_n),
            ];

            delete_key_side(&path);

            assert_eq!(1, n.links.as_ref().unwrap().len());
        }

        #[test]
        fn node_being_keyentry() {
            let mut empty_n = Node::empty();

            let mut n1 = Node::empty();
            n1.lrref = &n1;
            n1.links = Some(vec![Node::empty_boxed()]);

            let mut n2 = Node::empty();
            n2.links = Some(vec![Node::empty_boxed()]);

            #[rustfmt::skip]
            let path = vec![
                PathNode(usize::MAX, &mut empty_n),
                PathNode(usize::MAX, &mut n1),
                PathNode(0, &mut n2),
                PathNode(0, &mut empty_n),
            ];

            delete_key_side(&path);

            assert_eq!(false, n1.links());
            assert_eq!(false, n2.links());
        }

        #[test]
        fn root_escape() {
            let mut root = Node::empty();
            let node = Node::new_boxed('a', &root);
            root.links = Some(vec![node]);

            #[rustfmt::skip]
            let path = vec![
                PathNode(usize::MAX, &mut root),                
                PathNode(0, root.links.as_mut().unwrap()[0].deref_mut()),
            ];

            delete_key_side(&path);
            assert_eq!(None, root.links);
        }
    }

    mod delete_entry_side {
        use crate::{delete_entry_side, Links, Node};
        use std::{ops::Deref, ptr};

        #[test]
        fn keynode_with_links() {
            let mut n = Node::empty();
            n.supernode = &n;
            n.lrref = &n;
            n.links = Some(Links::new());

            delete_entry_side(&n);

            assert_eq!(ptr::null(), n.lrref);
        }

        #[test]
        fn node_with_links() {
            let mut n = Node::empty();
            n.supernode = &n;
            n.links = Some(vec![Node::new_boxed('a', &n), Node::empty_boxed()]);

            let mut ks_en = Node::empty();
            ks_en.lrref = n.links.as_ref().unwrap()[0].deref();

            delete_entry_side(&ks_en);

            let links = n.links.as_ref();
            assert!(links.is_some());
            let links = links.unwrap();

            assert_eq!(1, links.len());
            assert_eq!('\0', links[0].c);
        }

        #[test]
        fn node_being_keyentry() {
            let mut n = Node::empty();
            n.supernode = &n;
            n.links = Some(vec![Node::new_boxed('a', &n)]);
            n.lrref = &n;

            let mut ks_en = Node::empty();
            ks_en.lrref = n.links.as_ref().unwrap()[0].deref();

            delete_entry_side(&ks_en);

            assert_eq!(None, n.links);
        }

        #[test]
        fn root_escape() {
            let mut root = Node::empty();
            let node = Node::new_boxed('a', &root);
            root.links = Some(vec![node]);

            let mut ks_en = Node::empty();
            ks_en.lrref = root.links.as_ref().unwrap()[0].deref();

            delete_entry_side(&ks_en);
            assert_eq!(None, root.links);
        }
    }

    mod set_cap {

        use crate::{set_cap, UC};

        #[test]
        fn extend() {
            let new_cap = 10;

            let buf = UC::new(Vec::<usize>::new());
            assert!(buf.capacity() < new_cap);

            let size = set_cap(&buf, new_cap);
            assert!(size >= new_cap);
            assert!(buf.capacity() >= new_cap);
        }

        #[test]
        fn shrink() {
            let new_cap = 10;
            let old_cap = 50;

            let buf = UC::new(Vec::<usize>::with_capacity(old_cap));

            let size = set_cap(&buf, new_cap);
            assert!(size >= new_cap && size < old_cap);
            let cap = buf.capacity();
            assert!(cap >= new_cap && cap < old_cap);
        }

        #[test]
        fn same() {
            let cap = 10;
            let buf = UC::new(Vec::<usize>::new());

            assert!(buf.capacity() < cap);
            buf.get_mut().reserve_exact(cap);
            let cap = buf.capacity();

            let size = set_cap(&buf, cap);
            assert_eq!(cap, size);
            assert_eq!(cap, buf.capacity());
        }
    }

    mod ext {
        use crate::{ext, KeyEntry, LrTrie};

        #[test]
        fn basic_test() {
            let proof = [("opalescence", "black locust"), ("olivewood", "limehound")];

            let mut trie = LrTrie::new();
            for es in proof {
                trie.insert(&KeyEntry(es.0), &KeyEntry(es.1));
            }

            let mut k_buf = String::new();
            let mut res = Vec::new();

            let links = trie.left.links.as_ref().unwrap();
            let e_buf = trie.entry.get_mut();

            ext(links, &mut k_buf, e_buf, &mut res);

            assert_eq!(2, res.len());
            for z in proof.iter().zip(res.iter()) {
                let p = z.0;
                let t = z.1;

                assert_eq!(p.0, t.0);
                assert_eq!(p.1, t.1);
            }

            assert_eq!(0, k_buf.len());
            assert_eq!(0, e_buf.len());
        }

        #[test]
        fn load() {
            let proof = [
                ("olivenite", "limelight"),
                ("olivewood", "limehound"),
                ("olivary", "limestone"),
                ("oligotrophic", "limescale"),
                ("lemon", "bandoline"),
                ("lemonade", "podium"),
                ("lemon balm", "platina"),
                ("tapestry", "platform"),
                ("lemongrass", "rostrum"),
                ("temperate", "region"),
                ("tapis", "constituent"),
                ("cheque", "constellation"),
                ("season", "crops"),
                ("array", "formation"),
                ("glassware", "glasswork"),
            ];

            let mut trie = LrTrie::new();
            for es in proof {
                trie.insert(&KeyEntry(es.0), &KeyEntry(es.1));
            }

            let mut k_buf = String::new();
            let mut res = Vec::new();

            let links = trie.right.links.as_ref().unwrap();
            let e_buf = trie.entry.get_mut();

            ext(links, &mut k_buf, e_buf, &mut res);

            assert_eq!(proof.len(), res.len());
            for z in proof.iter().zip(res.iter()) {
                let p = z.0;
                let t = z.1;

                assert_eq!(p.1, t.0, "{}", p.0);
                assert_eq!(p.0, t.1, "{}", p.1);
            }
        }
    }

    mod construct_e {
        use crate::{construct_e, Node};

        #[test]
        fn construction() {
            let root = Node::empty();
            let n1 = Node::new('l', &root);
            let n2 = Node::new('r', &n1);
            let n3 = Node::new('_', &n2);
            let n4 = Node::new('t', &n3);
            let n5 = Node::new('r', &n4);
            let n6 = Node::new('i', &n5);
            let n7 = Node::new('e', &n6);

            let mut buf = Vec::new();

            let res = construct_e(&n7, &mut buf);
            assert_eq!("lr_trie", res.as_str());
            assert_eq!(0, buf.len());
        }

        #[test]
        fn root_escape() {
            let mut root = Node::empty();
            root.c = 'r';

            let mut buf = Vec::new();

            let res = construct_e(&root, &mut buf);
            assert_eq!("", res.as_str());
            assert_eq!(0, buf.len());
            assert_eq!(0, buf.capacity());
        }
    }

    mod trie {

        use crate::{uc::UC, LeftRight, LrTrie, Node};

        #[test]
        fn new() {
            let trie = LrTrie::new();
            let empty = Node::empty();

            assert_eq!(empty, trie.left);
            assert_eq!(empty, trie.right);
            assert_eq!(UC::new(Vec::new()), trie.trace);
            assert_eq!(UC::new(Vec::new()), trie.entry);
            assert_eq!(0, trie.count);
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
                let node = node.cast_mut();
                Node::as_mut(node).id = val;
            }

            #[test]
            fn basic_test() {
                let left_ke = &KeyEntry("LEFT");
                let right_ke = &KeyEntry("RIGHT");

                let trie = &mut LrTrie::new();
                trie.insert(left_ke, right_ke);

                assert_eq!(1, trie.count);

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
                let left_ke = &KeyEntry("LEFT");
                let right_ke = &KeyEntry("RIGHT");

                let trie = &mut LrTrie::new();

                let (lln_a_ptr, rln_a_ptr) = insert(trie, left_ke, right_ke);
                assert_eq!(1, trie.count);

                put_id(lln_a_ptr, 1);
                put_id(rln_a_ptr, 2);

                let (lln_b_ptr, rln_b_ptr) = insert(trie, left_ke, right_ke);
                assert_eq!(1, trie.count);

                let lln_b_ref = Node::as_ref(lln_b_ptr);
                let rln_b_ref = Node::as_ref(rln_b_ptr);

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
                let one = &KeyEntry("ONE");
                let another = &KeyEntry("ANOTHER");
                let replacement = &KeyEntry("REPLACEMENT");

                for lr in [LeftRight::Left, LeftRight::Right] {
                    let trie = &mut LrTrie::new();

                    let (lln_a_ptr, rln_a_ptr) = insert(trie, one, another);
                    assert_eq!(1, trie.count);

                    put_id(lln_a_ptr, 97);
                    put_id(rln_a_ptr, 98);

                    let (lln_b_ptr, rln_b_ptr) = if lr == LeftRight::Left {
                        insert(trie, replacement, another)
                    } else {
                        insert(trie, one, replacement)
                    };

                    assert_eq!(1, trie.count);

                    let (lln_b_ref, rln_b_ref) = (Node::as_ref(lln_b_ptr), Node::as_ref(rln_b_ptr));

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

            #[test]
            fn entry_map_merge() {
                let mut trie = LrTrie::new();

                let a1 = &KeyEntry("A1");
                let a2 = &KeyEntry("A2");
                let b1 = &KeyEntry("B1");
                let b2 = &KeyEntry("B2");

                trie.insert(a1, b1);
                trie.insert(b2, a2);

                assert_eq!(2, trie.count);
                trie.insert(a1, a2);
                assert_eq!(1, trie.count);

                assert_eq!(Some(a2.0.to_string()), trie.member(a1, LeftRight::Left));
                assert_eq!(Some(a1.0.to_string()), trie.member(a2, LeftRight::Right));

                assert_eq!(None, trie.member(b1, LeftRight::Right));
                assert_eq!(None, trie.member(b2, LeftRight::Left));
            }
        }

        mod insert_crux {
            use std::ops::Deref;

            use crate::{tra::TraStrain, Entry, KeyEntry, LeftRight, LrTrie, Node};

            #[test]
            fn basic_test() {
                let mut root = Node::empty();

                const ENTRY: &str = "lr_links_inserT";
                let limit = ENTRY.len() - 1;

                let entry: Entry = KeyEntry(ENTRY);
                let node = LrTrie::insert_crux(&mut root, &entry);

                assert_eq!('T', node.c);
                assert_eq!(None, node.links);

                assert!(root.links.is_some());

                let mut links = root.links.as_ref().unwrap();
                let mut super_n: *const Node = &root;
                for (ix, c) in ENTRY.chars().enumerate() {
                    let node = links.get(0);

                    assert!(node.is_some());
                    let node = node.unwrap();

                    assert_eq!(c, node.c);
                    assert_eq!(super_n, node.supernode);
                    super_n = node.deref();

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
                const OLD: &str = "touchstone";
                const NEW: &str = "touch";

                let old = KeyEntry(OLD);
                let new = KeyEntry(NEW);

                let mut trie = LrTrie::new();

                _ = LrTrie::insert_crux(&mut trie.left, &old);
                _ = LrTrie::insert_crux(&mut trie.left, &new);

                _ = trie.track(&old, LeftRight::Left, TraStrain::TraEmp);
                let old_path = trie.cc_trace();

                _ = trie.track(&new, LeftRight::Left, TraStrain::TraEmp);
                let new_path = trie.cc_trace();

                assert_eq!(OLD.len() + 1, old_path.len());
                assert_eq!(new_path, old_path[..NEW.len() + 1]);
            }
        }

        mod track {

            use crate::{KeyEntry, LeftRight, LrTrie, Node, TraRes, TraStrain};

            #[test]
            fn tracing() {
                let mut trie = LrTrie::new();

                let entries = ["key", "keyword", "keyboard", "keyhole"];
                let entries = entries.map(|x| KeyEntry(x));

                for e in entries.iter() {
                    trie.insert(&e, &e);
                }

                let keyword = &entries[1];
                _ = trie.track(keyword, LeftRight::Left, TraStrain::TraEmp);

                let trace = trie.cc_trace();

                assert_eq!(keyword.0.len() + 1, trace.len());

                let l_root: *const Node = &trie.left;
                assert_eq!(l_root as usize, trace[0].1 as usize);

                for k in entries[0..2].iter() {
                    let s = k.0;
                    for (ix, c) in s.chars().enumerate() {
                        let pn = &trace[ix + 1];
                        assert_eq!(0, pn.0);

                        let n = pn.n_ref();
                        assert_eq!(c, n.c);
                    }

                    let en = &trace[s.len()].n_ref();
                    assert_eq!(true, en.lrref());
                }

                _ = trie.track(&entries[3], LeftRight::Left, TraStrain::TraEmp);
                let trace = trie.cc_trace();

                let h_node = &trace[4];
                assert_eq!('h', h_node.n_ref().c);

                assert_eq!(2, h_node.0);
            }

            #[test]
            fn ok() {
                let entry = &KeyEntry("información meteorológica");

                let mut trie = LrTrie::new();
                _ = trie.insert(entry, entry);
                let res = trie.track(entry, LeftRight::Left, TraStrain::NonEmp);

                match res {
                    TraRes::Ok => {}
                    _ => panic!("Not `TraRes::Ok`, but {:?}.", res),
                }
            }

            #[test]
            fn ok_ref() {
                let entry = &KeyEntry("información meteorológica X");

                let mut trie = LrTrie::new();
                _ = trie.insert(entry, entry);
                let res = trie.track(entry, LeftRight::Left, TraStrain::NonRef);

                match res {
                    TraRes::OkRef(n) => {
                        assert_eq!(true, n.lrref());
                        assert_eq!('X', n.c);
                    }
                    _ => panic!("Not `TraRes::OkRef(_)`, but {:?}.", res),
                }
            }

            #[test]
            #[should_panic(expected = "Unsupported result scenario.")]
            fn unsupported_result() {
                let entry = &KeyEntry("información meteorológica");

                let mut trie = LrTrie::new();
                _ = trie.insert(entry, entry);

                _ = trie.track(entry, LeftRight::Left, TraStrain::NonMut);
            }

            #[test]
            fn unknown_not_path() {
                let entry = &KeyEntry("wordbook");
                let key = &KeyEntry("wordbooks");

                let mut trie = LrTrie::new();
                _ = trie.insert(entry, entry);
                let res = trie.track(key, LeftRight::Left, TraStrain::NonEmp);
                assert_eq!(TraRes::UnknownForAbsentPathLinks, res);
            }

            #[test]
            fn unknown_not_path2() {
                let entry = &KeyEntry("wordbookz");
                let key = &KeyEntry("wordbooks");

                let mut trie = LrTrie::new();
                _ = trie.insert(entry, entry);
                let res = trie.track(key, LeftRight::Left, TraStrain::NonEmp);
                assert_eq!(TraRes::UnknownForAbsentPathNode, res);
            }

            #[test]
            fn unknown_not_entry() {
                let entry = &KeyEntry("wordbooks");
                let key = &KeyEntry("wordbook");

                let mut trie = LrTrie::new();
                _ = trie.insert(entry, entry);

                let res = trie.track(key, LeftRight::Left, TraStrain::NonEmp);
                assert_eq!(TraRes::UnknownForNotEntry, res);
            }
        }

        mod member {

            use crate::{Entry, Key, KeyEntry, LeftRight, LrTrie};

            #[test]
            fn member() {
                let left_ke = KeyEntry("LEFT");
                let right_ke = KeyEntry("RIGHT");

                let mut trie = LrTrie::new();
                trie.insert(&left_ke, &right_ke);
                assert_eq!(0, trie.entry.capacity());

                verify(&left_ke, LeftRight::Left, &right_ke, &trie);
                verify(&right_ke, LeftRight::Right, &left_ke, &trie);

                fn verify(key: &Key, lr: LeftRight, e: &Entry, trie: &LrTrie) {
                    let entry = trie.member(key, lr);
                    assert!(entry.is_some());
                    assert_eq!(e.0, &entry.unwrap());
                    assert_eq!(0, trie.entry.len());
                    assert_eq!(true, trie.entry.capacity() > 0);
                }
            }

            #[test]
            fn not_member() {
                let keyword = KeyEntry("Keyword");

                let mut trie = LrTrie::new();
                trie.insert(&keyword, &keyword);

                for lr in [LeftRight::Left, LeftRight::Right] {
                    for key in ["Key", "Opener"] {
                        let key = KeyEntry(key);

                        let member = trie.member(&key, lr.clone());
                        assert!(member.is_none());
                    }
                }
            }
        }

        #[test]
        fn root() {
            let trie = LrTrie::new();

            let left = &trie.left as *const Node as usize;
            let right = &trie.right as *const Node as usize;

            let vals = [(left, LeftRight::Left), (right, LeftRight::Right)];
            for v in vals {
                let test = trie.root(v.1) as *const Node as usize;
                assert_eq!(v.0, test);
            }
        }

        /// Node in path to entry being deleted
        /// cannot be deleted if and only if participates
        /// in path to another entry. Path len varies 0…m.
        mod delete {

            use crate::{tra::TraStrain, Key, KeyEntry, LeftRight, LrTrie};

            #[test]
            fn known_unknown() {
                let known = &KeyEntry("plainoperator");
                let unknown = &KeyEntry("secretagent");

                let mut trie = LrTrie::new();
                _ = trie.insert(&known, &known);

                assert_eq!(Err(()), trie.delete(&unknown, LeftRight::Left));
                assert_eq!(0, trie.trace.len());
                assert_eq!(1, trie.count);

                assert_eq!(Ok(()), trie.delete(&known, LeftRight::Left));
                assert_eq!(0, trie.trace.len());
                assert_eq!(0, trie.count);
                assert_eq!(None, trie.member(&known, LeftRight::Right));
            }

            #[test]
            fn inner_entry() {
                let mut trie = LrTrie::new();

                let outer = KeyEntry("Keyword");
                trie.insert(&outer, &outer);

                for lr in [LeftRight::Left, LeftRight::Right] {
                    let inner = KeyEntry("Key");
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
                let keyword = KeyEntry("Keyword");
                let keyboard = KeyEntry("Keyboard");
                let keypad = KeyEntry("Keypad");
                let key: Key = KeyEntry("Key");

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

                        _ = trie.track(&key, lr, TraStrain::TraEmp);
                        let y_node = trie.trace[key.0.len()].n_ref();
                        let links = y_node.links.as_ref().unwrap();
                        assert_eq!(2, links.len());
                        let filtered = links.iter().filter(|x| x.c == 'w' || x.c == 'p').count();
                        assert_eq!(2, filtered);
                    }
                }
            }

            #[test]
            fn links_removal() {
                let keyword = KeyEntry("Keyword");
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
                let dissimilar = KeyEntry("Dissimilar");
                let keyword = KeyEntry("Keyword");

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
            fn node_being_keyentry() {
                let keyword = KeyEntry("Keyword");
                let k = KeyEntry("K");

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

        mod put_buf_cap {
            use crate::{Buffer, LrTrie};

            #[test]
            fn trace() {
                let mut trie = LrTrie::new();
                assert_eq!(0, trie.trace.capacity());

                let cap = 100;
                let size = trie.put_buf_cap(cap, Buffer::Delete);
                assert_eq!(true, size >= cap);
                assert_eq!(true, trie.trace.capacity() >= cap);
            }

            #[test]
            fn entry() {
                let mut trie = LrTrie::new();
                assert_eq!(0, trie.entry.capacity());

                let cap = 100;
                let size = trie.put_buf_cap(cap, Buffer::Member);
                assert_eq!(true, size >= cap);
                assert_eq!(true, trie.entry.capacity() >= cap);
            }
        }

        mod aq_buf_cap {
            use crate::{Buffer, LrTrie};

            #[test]
            fn trace() {
                let cap = 10;
                let trie = LrTrie::new();
                let buf = trie.trace.get_mut();

                assert!(buf.capacity() < cap);
                buf.reserve_exact(cap);
                let cap = buf.capacity();

                assert_eq!(cap, trie.aq_buf_cap(Buffer::Delete));
            }

            #[test]
            fn entry() {
                let cap = 10;
                let trie = LrTrie::new();
                let buf = trie.entry.get_mut();

                assert!(buf.capacity() < cap);
                buf.reserve_exact(cap);
                let cap = buf.capacity();

                assert_eq!(cap, trie.aq_buf_cap(Buffer::Member));
            }
        }
    }

    use crate::KeyEntry;
    #[test]
    fn clear() {
        let mut trie = LrTrie::new();
        let entry = KeyEntry("Key");
        trie.insert(&entry, &entry);

        trie.clear();

        assert_eq!(0, trie.count);

        assert_eq!(trie.left, Node::empty());
        assert_eq!(trie.right, Node::empty());
        assert_eq!(trie, LrTrie::new());
    }

    #[test]
    fn count() {
        let mut trie = LrTrie::new();
        assert_eq!(0, trie.count());

        trie.count = 99;

        assert_eq!(99, trie.count());
    }

    // exercise logic in greater deep
    #[test]
    fn load_1() {
        const P_LEN: usize = 15;
        let proof: [(&str, &str); P_LEN] = [
            ("olivenite", "limelight"),
            ("olivewood", "limehound"),
            ("olivary", "limestone"),
            ("oligotrophic", "limescale"),
            ("lemon", "bandoline"),
            ("lemonade", "podium"),
            ("lemongrass", "rostrum"),
            ("lemon balm", "platina"),
            ("tapestry", "platform"),
            ("tapis", "constituent"),
            ("temperate", "region"),
            ("cheque", "constellation"),
            ("array", "formation"),
            ("season", "crops"),
            ("glassware", "glasswork"),
        ];

        let mut trie = LrTrie::new();
        for es in proof {
            trie.insert(&KeyEntry(es.0), &KeyEntry(es.1));
        }
        for p in proof {
            let entry = trie.member(&KeyEntry(p.0), LeftRight::Left);
            assert_eq!(p.1, entry.unwrap().as_str());

            let entry = trie.member(&KeyEntry(p.1), LeftRight::Right);
            assert_eq!(p.0, entry.unwrap().as_str());
        }

        for i in 0..P_LEN {
            if i & 1 == 0 {
                assert_eq!(Ok(()), trie.delete(&KeyEntry(proof[i].0), LeftRight::Left));
            }
        }

        for i in 0..P_LEN {
            let p = proof[i];

            if i & 1 == 1 {
                let entry = trie.member(&KeyEntry(p.0), LeftRight::Left);
                assert_eq!(p.1, entry.unwrap().as_str());

                let entry = trie.member(&KeyEntry(p.1), LeftRight::Right);
                assert_eq!(p.0, entry.unwrap().as_str());
            } else {
                let entry = trie.member(&KeyEntry(p.0), LeftRight::Left);
                assert_eq!(true, entry.is_none());

                let entry = trie.member(&KeyEntry(p.1), LeftRight::Right);
                assert_eq!(true, entry.is_none());
            }
        }
    }

    // exercise logic in greater deep
    #[test]
    fn load_2() {
        const P_LEN: usize = 15;
        let last_ix = P_LEN - 1;
        let proof: [(&str, &str); P_LEN] = [
            ("olivenite", "limelight"),
            ("olivewood", "limehound"),
            ("olivary", "limestone"),
            ("oligotrophic", "limescale"),
            ("lemon", "bandoline"),
            ("lemonade", "podium"),
            ("lemongrass", "rostrum"),
            ("lemon balm", "platina"),
            ("tapestry", "platform"),
            ("tapis", "constituent"),
            ("temperate", "region"),
            ("cheque", "constellation"),
            ("array", "formation"),
            ("season", "crops"),
            ("glassware", "glasswork"),
        ];

        let mut trie = LrTrie::new();
        for es in proof {
            trie.insert(&KeyEntry(es.0), &KeyEntry(es.1));
        }
        for p in proof {
            let entry = trie.member(&KeyEntry(p.0), LeftRight::Left);
            assert_eq!(p.1, entry.unwrap().as_str());

            let entry = trie.member(&KeyEntry(p.1), LeftRight::Right);
            assert_eq!(p.0, entry.unwrap().as_str());
        }

        for i in 1..last_ix {
            assert_eq!(Ok(()), trie.delete(&KeyEntry(proof[i].1), LeftRight::Right));
        }

        for i in 1..last_ix {
            let p = proof[i];

            assert_eq!(None, trie.member(&KeyEntry(p.0), LeftRight::Left));
            assert_eq!(None, trie.member(&KeyEntry(p.1), LeftRight::Right));
        }

        for i in [0, last_ix] {
            let p = proof[i];

            let entry = trie.member(&KeyEntry(p.0), LeftRight::Left);
            assert_eq!(p.1, entry.unwrap().as_str());

            let entry = trie.member(&KeyEntry(p.1), LeftRight::Right);
            assert_eq!(p.0, entry.unwrap().as_str());
        }
    }

    mod readme {
        use crate::{KeyEntry, LeftRight, LrTrie};

        #[test]
        fn test() {
            let mut trie = LrTrie::new();
            let one = KeyEntry("emoción");
            let another = KeyEntry("emotion");

            trie.insert(&one, &another);
            assert!(trie.member(&one, LeftRight::Left).is_some());
            assert!(trie.member(&another, LeftRight::Left).is_none());
            assert!(trie.member(&another, LeftRight::Right).is_some());
        }
    }
}

// cargo test --release
