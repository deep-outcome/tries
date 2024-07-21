use std::collections::hash_map::HashMap;

type Links<T> = HashMap<char, Node<T>>;
type Path<'a, T> = Vec<PathNode<'a, T>>;
type PathNode<'a, T> = (char, &'a Node<T>);

fn entry_path_node<'a, T>(path: &Path<'a, T>, key: &str) -> Option<PathNode<'a, T>> {
    let key_len = key.len();
    if path.len() < key_len + 1 {
        None
    } else {
        let epn = path[key_len];
        if epn.1.entry() {
            Some(epn)
        } else {
            None
        }
    }
}

/// Retrieval tree implementation allowing for mapping any `T` to any string.
///
/// Every node is `char` as defined by Rust lang and uses `std::collections::HashMap`
/// to linking subnodes. Thus all methods complexity is respective to hashmap methods complexity.
pub struct Trie<T> {
    root: Node<T>,
}

/// Key validated for usage with `Trie`.
pub struct Key<'a>(&'a str);

impl<'a> Key<'a> {
    /// `None` for 0-len `key`.
    pub fn new(key: &'a str) -> Option<Self> {
        if key.len() == 0 {
            None
        } else {
            Some(Self(key))
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

const NULL: char = '\0';
impl<T> Trie<T> {
    /// Ctor.
    pub fn new() -> Trie<T> {
        Trie {
            root: Node::<T>::empty(),
        }
    }

    pub fn insert(&mut self, entry: T, key: &Key) {
        let mut node = &mut self.root;
        for c in key.chars() {
            let links = node.links.get_or_insert_with(|| Links::new());
            node = links.entry(c).or_insert(Node::<T>::empty());
        }

        node.entry = Some(entry);
    }

    /// `None` for unknown key.
    pub fn member(&self, key: &Key) -> Option<&T> {
        let key = key.0;
        let path = self.path(key);

        let epn = entry_path_node(&path, key);

        if let Some(epn) = epn {
            epn.1.entry.as_ref()
        } else {
            None
        }
    }

    /// `Err` for unknown key.
    pub fn delete(&mut self, key: &Key) -> Result<(), ()> {
        let key = key.0;
        let path = self.path(key);
        let entry_pn = match entry_path_node(&path, key) {
            Some(epn) => epn,
            _ => return Err(()),
        };

        let entry_n = entry_pn.1;
        if entry_n.links() {
            unsafe { as_mut(entry_n) }.entry = None; // Sounds.
            return Ok(());
        }

        let mut path_rev = path.iter().rev();
        _ = path_rev.next();

        let mut subnode_key = entry_pn.0;
        while let Some((c, n)) = path_rev.next() {
            let n_mut = unsafe { as_mut(*n) }; // Sounds.

            let n_links = n_mut.links.as_mut().unwrap();
            _ = n_links.remove(&subnode_key);

            let c = *c;
            if n_links.len() == 0 {
                n_mut.links = None;
            } else {
                return Ok(());
            }

            if n.entry() {
                return Ok(());
            }

            subnode_key = c;
        }

        return Ok(());

        unsafe fn as_mut<T>(node: &Node<T>) -> &mut Node<T> {
            let ptr: *const Node<T> = node;
            let mut_ptr: *mut Node<T> = std::mem::transmute(ptr);
            mut_ptr.as_mut().unwrap()
        }
    }

    fn path(&self, key: &str) -> Vec<PathNode<'_, T>> {
        let root = &self.root;
        let mut links = root.links.as_ref();

        let mut path = Vec::with_capacity(key.len() + 1);
        path.push((NULL, root));

        for c in key.chars() {
            if let Some(l) = links {
                if let Some(node) = l.get(&c) {
                    path.push((c, node));
                    links = node.links.as_ref();

                    continue;
                }
            }

            break;
        }

        path
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

    mod entry_path_node {
        use crate::{entry_path_node, Node, NULL};

        fn replacement_key(n: usize) -> String {
            const REPLACEMENT: char = '\u{001A}';

            REPLACEMENT.to_string().repeat(n)
        }

        /// Longer key means it is not traced by path.
        #[test]
        fn longer_key() {
            const PATH_LEN: usize = 4;

            let node: Node<usize> = Node::empty();
            let path = vec![(NULL, &node); PATH_LEN];
            let key = replacement_key(PATH_LEN);

            assert_eq!(None, entry_path_node(&path, &key));
        }

        #[test]
        fn not_entry() {
            const PATH_LEN: usize = 5;

            let node: Node<usize> = Node::empty();
            let path = vec![(NULL, &node); PATH_LEN];
            let key = replacement_key(PATH_LEN - 1);

            assert_eq!(None, entry_path_node(&path, &key));
        }

        #[test]
        fn entry() {
            let empty_n: Node<usize> = Node::empty();

            let mut entry_n = empty_n.clone();
            entry_n.entry = Some(0);

            let mut path = vec![(NULL, &empty_n); 4];
            path.push(('a', &entry_n));

            let key = replacement_key(4);

            let epn = entry_path_node(&path, &key);
            assert!(epn.is_some());
            let epn = epn.unwrap();
            assert_eq!('a', epn.0);
            assert!(epn.1.entry());
        }
    }

    mod key {
        use crate::Key;

        mod new {
            use crate::Key;

            #[test]
            fn some() {
                const KEY: &str = "key";
                let key = Key::new(KEY);
                assert!(key.is_some());
                assert_eq!(KEY, key.unwrap().0);
            }

            #[test]
            fn none() {
                const EMPTY: &str = "";
                let key = Key::new(EMPTY);
                assert!(key.is_none());
            }
        }

        use std::ops::Deref;

        #[test]
        fn deref() {
            const KEY: &str = "key";
            let key = Key::new(KEY).unwrap();
            assert_eq!(KEY, key.deref());
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
        }

        mod insert {
            use crate::{Key, Trie};

            #[test]
            fn basic_test() {
                const KEY: &str = "touchstone";

                let mut trie = Trie::new();
                trie.insert(3usize, &Key::new(KEY).unwrap());

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
                let existing = Key::new("touchstone").unwrap();
                let new = Key::new("touch").unwrap();

                let mut trie = Trie::new();
                trie.insert(3usize, &existing);
                trie.insert(4usize, &new);

                assert!(trie.member(&existing).is_some());
                assert!(trie.member(&new).is_some());
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

                for key in ["Key", "Opener"] {
                    let key = Key::new(key).unwrap();
                    let member = trie.member(&key);
                    assert!(member.is_none());
                }
            }
        }

        /// Node in path to entry being deleted
        /// cannot be deleted if and only if participates
        /// in path to another entry. Path len varies 0…m.        
        mod delete {

            use crate::{Key, Trie};

            #[test]
            fn not_member() {
                let key = Key::new("Keyword").unwrap();
                let mut trie = Trie::new();
                trie.insert(0usize, &key);

                for bad_key in ["Key", "Opener"] {
                    let bad_key = Key::new(bad_key).unwrap();
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
            fn links_removal() {
                let key = Key::new("Keyword").unwrap();
                let mut trie = Trie::new();
                trie.insert(0usize, &key);

                assert!(trie.delete(&key).is_ok());
                assert!(trie.member(&key).is_none());
                let links = trie.root.links;
                assert!(links.is_none());
            }

            #[test]
            fn node_composing_path() {
                let dissimilar = Key::new("Dissimilar").unwrap();
                let keyword = Key::new("Keyword").unwrap();

                let mut trie = Trie::new();
                trie.insert(0usize, &dissimilar);
                trie.insert(0usize, &keyword);

                assert!(trie.delete(&keyword).is_ok());
                assert!(trie.member(&keyword).is_none());
                assert!(trie.member(&dissimilar).is_some());
            }

            #[test]
            fn node_being_entry() {
                let key1 = Key::new("Keyword").unwrap();
                let key2 = Key::new("K").unwrap();
                let mut trie = Trie::new();
                trie.insert(0usize, &key1);
                trie.insert(0usize, &key2);

                assert!(trie.delete(&key1).is_ok());
                assert!(trie.member(&key1).is_none());
                assert!(trie.member(&key2).is_some());

                let k = trie.root.links.as_ref().unwrap().get(&'K');
                assert!(!k.unwrap().links());
            }
        }

        mod path {

            use crate::{Key, Trie, NULL};

            #[test]
            fn path() {
                let mut trie = Trie::<usize>::new();

                let kvs = [("k", 12), ("keyw", 22), ("keyword", 45)];
                for (k, v) in kvs {
                    let k = Key::new(k).unwrap();
                    trie.insert(v, &k);
                }

                let keyword = kvs[2].0;
                let proof = format!("{}{}", NULL, keyword);

                let path = trie.path(keyword);
                assert_eq!(proof.len(), path.len());

                let mut ix = 0;
                for c in proof.chars() {
                    let p = path[ix];
                    assert_eq!(c, p.0);
                    ix += 1;
                }

                for (k, v) in kvs {
                    let (_, node) = path[k.len()];
                    assert!(node.entry());
                    assert_eq!(v, node.entry.unwrap());
                }
            }

            #[test]
            fn no_branch() {
                let mut trie = Trie::<usize>::new();

                let keyboard = Key::new("Keyboard").unwrap();
                let keyword = Key::new("Keyword").unwrap();
                trie.insert(0usize, &keyword);

                let path = trie.path(&keyboard);
                let proof = format!("{}Key", NULL);
                assert_eq!(proof.len(), path.len());

                let mut ix = 0;
                for c in proof.chars() {
                    let p = path[ix];
                    assert_eq!(c, p.0);
                    ix += 1;
                }
            }

            #[test]
            fn no_branches() {
                const KEY: &str = "Key";
                let trie = Trie::<usize>::new();

                let path = trie.path(KEY);
                assert_eq!(1, path.len());
                assert_eq!(NULL, path[0].0);
            }
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
}
