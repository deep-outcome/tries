//! Poetrie, poetic trie, is trie designated for finding rhymes for your verses.
//!
//! For given input, and populated tree, it will find words with shared suffix for you.

#![allow(for_loops_over_fallibles)]

use std::{cmp::min, collections::hash_map::HashMap, ops::Deref, ptr};

mod uc;
use uc::UC;

type Links = HashMap<char, Node>;
type Find = Vec<String>;
type WordBuf = Vec<char>;
// branching information
type BraInf = Vec<(*const HashMap<char, Node>, usize)>;

fn get_node<'a>(l: &'a Links, c: &char, #[cfg(test)] ecode: &mut usize) -> Option<&'a Node> {
    let g = l.get(c);
    if g.is_some() {
        #[cfg(test)]
        set_ecode(1, ecode);

        return g;
    }

    let iter: &mut dyn ExactSizeIterator<Item = char> = if c.is_lowercase() {
        #[cfg(test)]
        set_ecode(2, ecode);

        &mut c.to_uppercase()
    } else if c.is_uppercase() {
        #[cfg(test)]
        set_ecode(4, ecode);

        &mut c.to_lowercase()
    } else {
        #[cfg(test)]
        set_ecode(8, ecode);

        return None;
    };

    return if iter.len() == 1 {
        #[cfg(test)]
        set_ecode(32, ecode);

        let c = unsafe { iter.next().unwrap_unchecked() };
        l.get(&c)
    } else {
        #[cfg(test)]
        set_ecode(16, ecode);

        None
    };

    #[cfg(test)]
    fn set_ecode(c: usize, ecode: &mut usize) {
        let code = *ecode;
        *ecode = code | c;
    }
}

fn extract(l: &Links, buff: &mut WordBuf, o: &mut Vec<String>) {
    for (k, n) in l.iter() {
        buff.push(*k);

        if n.entry {
            let entry = buff.iter().rev().collect();
            o.push(entry);
        }

        if let Some(l) = n.links.as_ref() {
            extract(l, buff, o);
        }

        _ = buff.pop();
    }
}

struct Extender<'a> {
    b: &'a mut WordBuf,
    f: &'a mut Find,
    n: usize,
    // max length
    xl: usize,
    // min length
    nl: usize,
}

impl<'a> Extender<'a> {
    pub fn e(&mut self, n: &Node, c: char) -> bool {
        let b = &mut self.b;
        b.push(c);

        let b_len = b.len();
        let xl = self.xl;

        #[cfg(test)]
        assert!(b_len <= xl, "Caller disobeys precondition.");

        if n.entry {
            if self.nl <= b_len && push_match(b, self.f, self.n) {
                return true;
            }
        }

        if b_len < xl {
            if let Some(l) = n.links.as_ref() {
                for (c, node) in l.iter() {
                    if self.e(node, *c) {
                        return true;
                    }
                }
            }
        }

        _ = self.b.pop();

        false
    }
}

fn push_match(c: &[char], f: &mut Find, l: usize) -> bool {
    let e = c.iter().rev().collect();
    f.push(e);

    f.len() == l
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

/// Various match behavior requirement errors.
#[derive(Debug, Clone, PartialEq)]
pub enum ReqErr {
    /// Matches can be limited to one at least.
    ZeroMaxMatches,
    /// Suffix match is posed by at least one `char` match.
    ZeroMinSufLen,
    /// Maximal suffix match length cannot be less than minimal.
    SufLenMaxLessThanMin,
    /// Maximal match length cannot be less than minimal.    
    MatchLenMaxLessThanMin,

    #[cfg(test)]
    MatchLenMinLessThanSufLenMin,
}

/// [`MatchConduct`] default values.
pub mod mc_defaults {
    /// Matches limit default.
    pub const MAX_N: usize = 1;
    /// Minimum suffix match length default.
    pub const MIN_SL: usize = 1;
    /// Maximum suffix match length default.
    pub const MAX_SL: usize = usize::MAX;
    /// Match extra length requirement default.
    pub const EXT_ML: usize = 0;
    /// Maximal match length default.
    pub const MAX_ML: usize = usize::MAX;
    /// Sub-entries inclusion flag default.
    pub const SUB_E: bool = false;
}

/// Requirements for [`Poetrie::sx`] match behavior adjustments.
#[derive(Debug, Clone, PartialEq)]
pub struct MatchConduct {
    // max matches
    max_n: usize,
    // min suffix match length
    min_sl: usize,
    // max suffix match length
    max_sl: usize,
    // min match length
    min_ml: usize,
    // max match length
    max_ml: usize,
    // sub-entries inclusion
    sub_e: bool,
}

use crate::mc_defaults::*;
impl MatchConduct {
    /// Parameterized constructor:
    ///
    /// - `max_n` – matches limit.
    /// - `min_sl` – minimal suffix match length.
    /// - `max_sl` – maximal suffix match length.
    /// - `ext_ml` – extra length requirement used for minimal match length computation using formula `min_ml =min_sl +ext_ml`.
    /// - `max_ml` – maximal match length.
    /// - `sub_e` – sub-entries inclusion flag.
    ///
    /// Every parameter provided with `None` will use default as expressed at [`MatchConduct::default`].
    ///
    /// Inputs are validated for various conditions in non-exhaustive plan, first
    /// error encountered is returned. See [`ReqErr`] for details.
    pub fn new(
        max_n: Option<usize>,
        min_sl: Option<usize>,
        max_sl: Option<usize>,
        ext_ml: Option<usize>,
        max_ml: Option<usize>,
        sub_e: Option<bool>,
    ) -> Result<MatchConduct, ReqErr> {
        let max_n = max_n.unwrap_or(MAX_N);
        let min_sl = min_sl.unwrap_or(MIN_SL);
        let max_sl = max_sl.unwrap_or(MAX_SL);
        let ext_ml = ext_ml.unwrap_or(EXT_ML);
        let max_ml = max_ml.unwrap_or(MAX_ML);
        let sub_e = sub_e.unwrap_or(SUB_E);

        let min_ml = min_sl + ext_ml;
        let new = Self {
            max_n,
            min_sl,
            max_sl,
            min_ml,
            max_ml,
            sub_e,
        };

        if let Some(e) = Self::val(&new) {
            Err(e)
        } else {
            Ok(new)
        }
    }

    /// Parameterless constructor.
    ///
    /// Defaults:
    /// - `max_n` = [`mc_defaults::MAX_N`].
    /// - `min_sl` = [`mc_defaults::MIN_SL`].
    /// - `max_sl` = [`mc_defaults::MAX_SL`].
    /// - `ext_ml` = [`mc_defaults::EXT_ML`].
    /// - `max_ml` = [`mc_defaults::MAX_ML`].
    /// - `sub_e` = [`mc_defaults::SUB_E`].
    ///
    /// Check with [`MatchConduct::new`] for details.
    pub fn default() -> MatchConduct {
        let new = Self {
            max_n: MAX_N,
            min_sl: MIN_SL,
            max_sl: MAX_SL,
            min_ml: MIN_SL + EXT_ML,
            max_ml: MAX_ML,
            sub_e: SUB_E,
        };

        #[cfg(test)]
        Self::val(&new);

        new
    }

    fn val(s: &Self) -> Option<ReqErr> {
        #[cfg(test)]
        if s.min_ml < s.min_sl {
            return Some(ReqErr::MatchLenMinLessThanSufLenMin);
        }

        let min_sl = s.min_sl;

        let err = if s.max_n == 0 {
            ReqErr::ZeroMaxMatches
        } else if min_sl == 0 {
            ReqErr::ZeroMinSufLen
        } else if s.max_sl < min_sl {
            ReqErr::SufLenMaxLessThanMin
        } else if s.max_ml < s.min_ml {
            ReqErr::MatchLenMaxLessThanMin
        } else {
            return None;
        };

        Some(err)
    }

    fn max_l(&self) -> usize {
        min(self.max_ml, self.max_sl)
    }
}

/// Chain-of-adjustments refining type.
///
/// Use various _with_ methods to adjust [`MatchConduct`]
/// values as desired.
///
/// Check with [`MatchConduct::new`] for detailed explanation.
///
/// ```
/// use poetrie::{MatchConductWith, MatchConduct};
///
/// let mut chain = MatchConductWith::init();
/// _ = chain.with_max_n(10).with_max_ml(8);
///
/// let mc: MatchConduct = chain.with().unwrap();
#[derive(Debug, Clone, PartialEq)]
pub struct MatchConductWith(MatchConduct);

impl MatchConductWith {
    /// Use to construct new `MatchConductWith` instance.
    ///
    /// Constructed with [`MatchConduct::default()`] as initial value.
    ///
    /// Check with [`MatchConductWith::with`] for more details.
    pub fn init() -> MatchConductWith {
        Self(MatchConduct::default())
    }

    /// Use to adjust matches limit.
    pub fn with_max_n(&mut self, max_n: usize) -> &mut Self {
        self.0.max_n = max_n;
        self
    }

    /// Use to adjust minimal suffix match length.
    pub fn with_min_sl(&mut self, min_sl: usize) -> &mut Self {
        self.0.min_sl = min_sl;
        self
    }

    /// Use to adjust maximal suffix match length.
    pub fn with_max_sl(&mut self, max_sl: usize) -> &mut Self {
        self.0.max_sl = max_sl;
        self
    }

    /// Use to adjust extra match length requirement.
    pub fn with_ext_ml(&mut self, ext_ml: usize) -> &mut Self {
        let mc = &mut self.0;
        mc.min_ml = mc.min_sl + ext_ml;
        self
    }

    /// Use to adjust maximal match length.
    pub fn with_max_ml(&mut self, max_ml: usize) -> &mut Self {
        self.0.max_ml = max_ml;
        self
    }

    /// Use to adjust sub-entries inclusion flag.
    pub fn with_sub_e(&mut self, sub_e: bool) -> &mut Self {
        self.0.sub_e = sub_e;
        self
    }

    /// Use to validate `MatchConduct` instance.
    ///
    /// Return value is `Result` with either valid `MatchConduct`
    /// instance or with [`ReqErr`] error information.
    pub fn with(&self) -> Result<MatchConduct, ReqErr> {
        if let Some(e) = MatchConduct::val(&self.0) {
            Err(e)
        } else {
            Ok(self.0.clone())
        }
    }
}

/// Poetrie is poetic retrieval tree implementation for finding words with shared suffixes.
///
/// Inputs are validated only for 0 length thus is up to consumer code
/// to allow population with sensible values only.
pub struct Poetrie {
    root: Node,
    // backtrace buff
    btr: UC<Vec<(char, *mut Node)>>,
    // sufix-word buffer
    buf: UC<WordBuf>,
    // branching information
    bra: UC<BraInf>,
    // entries count
    cnt: usize,
}

const NULL: char = '\0';
impl Poetrie {
    /// Use for `Poetrie` construction.
    pub const fn nw() -> Poetrie {
        Poetrie {
            root: Node::empty(),
            btr: UC::new(Vec::new()),
            buf: UC::new(Vec::new()),
            bra: UC::new(Vec::new()),
            cnt: 0,
        }
    }

    /// Use for entry insertions into tree.
    ///
    /// Return value is `true` if entry was inserted into tree,
    /// `false` if it was present already.
    pub fn it(&mut self, entry: &Entry) -> bool {
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
    pub fn ey(&self, key: &Key) -> bool {
        let res = self.track(key, false);

        TraRes::Ok == res
    }

    /// Use to find entries with shared suffix to key.
    ///
    /// Generally, suffix match length is emphasized, entries are ordered
    /// from that with longest suffix match to those with shortest suffix match.
    /// With exception for sub-entries which are ordered very first, at list beginning.
    ///
    /// Sub-entries are entries which are suffix to picked key, e.g. for _commode_
    /// _ode_ and _mode_ are its sub-entries.
    ///
    /// Other type of match is shared suffix that occurs when:
    /// - Key shares partially its suffix with other word, like _parade_ with _charade_.
    /// - Key itself is suffix to some entry, like _ant_ to _blatant_.
    ///
    /// By obvious means minimal suffix match length is 1 `char`.
    ///
    /// Use `mc` to express matching behavior adjustments. Check with [`MatchConduct::new()`]
    /// or [`MatchConductWith`] for details.
    ///
    /// For instance, having _password_ as key, _word_ sounds weird as rhyme, so
    /// subentries should be avoided. However, similar applies to other words, e.g.
    /// _catchword_ rhymes evenly bad. For this maximal suffix match length can be used.
    /// However, then word _sword_ cannot be matched and open riddle like this created
    ///
    /// _Secrets I do,_
    /// _hide for you._
    /// _Shattered, still whole,_
    /// _robbed now your role._
    /// _Buried down, laid,_
    /// _a self-clown raid._
    /// _What am I?_
    /// _(Fair, blameless pass-sword.)_
    ///
    /// It could be not all words are enough long or on flip side some are excessively long.
    /// Drive this by extra length added to minimal suffix match length and by maximal match
    /// word length. Finally, hardly anybody would find words like _middle_ and _harmonize_
    /// rhyming only because _e_ ending. Use minimal suffix match length to overcome unsound match.
    ///
    /// ```
    /// use poetrie::{MatchConductWith, MatchConduct};
    ///
    /// let mut with = MatchConductWith::init();
    /// with
    ///    .with_min_sl(3).with_max_sl(5).with_ext_ml(1)
    ///    .with_max_ml(10).with_sub_e(false).with_max_n(15);
    ///
    /// let mc: MatchConduct = with.with().unwrap();
    /// ```
    ///
    /// This and only this method is case insensitive. Exactly, if char
    /// in question provides one-to-one mapping as described at
    /// [`char::to_lowercase`] and [`char::to_uppercase`], attempt to find
    /// other casing on miss is made.
    ///
    /// Case insesitivy is wild as it uses key casing for result as long
    /// as it is possible. Let check with example bellow.
    /// ```
    /// use poetrie::{Poetrie, Entry, MatchConduct};
    ///
    /// let entry = Entry::new_from_str("ForenOOn").unwrap();
    ///
    /// let mut poetrie = Poetrie::nw();
    /// _ = poetrie.it(&entry);
    ///
    /// let key = Entry::new_from_str("NooN").unwrap();
    /// let mc = MatchConduct::default();
    /// let find = poetrie.sx(&key, &mc);
    ///
    /// let proof = String::from("ForeNooN");
    /// assert_eq!(Ok(vec![proof]), find);
    /// ```
    pub fn sx(&self, key: &Key, mc: &MatchConduct) -> Result<Vec<String>, FindErr> {
        let res = self.find(
            key,
            mc,
            #[cfg(test)]
            &mut 0,
        );

        self.clr_f_buffs();

        return res;
    }

    fn clr_f_buffs(&self) {
        self.bra.get_mut().clear();
        self.buf.get_mut().clear();
    }

    /// Use to remove entry from tree.
    ///
    /// Return value is `true` if entry was removed, `false` if it was not present.
    pub fn re(&mut self, entry: &Entry) -> bool {
        let tra_res = self.track(entry, true);
        let res = if let TraRes::Ok = tra_res {
            self.re_actual(
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

    fn re_actual(&mut self, #[cfg(test)] esc_code: &mut usize) {
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

    fn find(
        &self,
        key: &Key,
        mc: &MatchConduct,
        #[cfg(test)] b_code: &mut usize,
    ) -> Result<Find, FindErr> {
        // operative node
        let mut op_node = &self.root;
        if op_node.links.is_none() {
            return Err(FindErr::EmptyTree);
        }

        let max_n = mc.max_n;
        let min_sl = mc.min_sl;
        let min_ml = mc.min_ml;
        let max_ml = mc.max_ml;
        let sub_entries = mc.sub_e;

        // closest branch information
        let branching = self.bra.get_mut();
        let mut skip_n = ptr::null();
        let mut se_disjunct_hit = false;

        // finds
        let mut find = Vec::with_capacity(100);

        // match
        let buff = self.buf.get_mut();
        let mut buf_l;

        let max_l = mc.max_l();

        let mut chars = key.chars();
        // track key as much as possible first
        'track: loop {
            buf_l = buff.len();

            let next_c = chars.next_back();

            if next_c.is_none() {
                #[cfg(test)]
                set_bcode(2, b_code);
                break 'track;
            }

            if op_node.entry {
                if sub_entries && min_ml <= buf_l {
                    if push_match(buff, &mut find, max_n) {
                        #[cfg(test)]
                        set_bcode(64, b_code);
                        return Ok(find);
                    }
                } else {
                    se_disjunct_hit = true;
                }
            }

            if buf_l == max_l {
                #[cfg(test)]
                set_bcode(1024, b_code);
                break;
            }

            if let Some(l) = op_node.links.as_ref() {
                let c = unsafe { next_c.unwrap_unchecked() };

                if let Some(n) = get_node(
                    l,
                    &c,
                    #[cfg(test)]
                    &mut 0,
                ) {
                    if l.len() > 1 && min_sl <= buf_l {
                        skip_n = n;
                        branching.push((l, buf_l));
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

        if buf_l == 0 {
            return Err(FindErr::NoJointSuffix);
        }

        if buf_l < min_sl {
            return Err(FindErr::DisjunctConduct);
        }

        let links = op_node.links.as_ref();
        let can_extend = links.is_some() && buf_l < max_ml;

        let can_branch = branching.len() > 0;

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

        if !(can_extend || can_branch) {
            if find.len() == 0 {
                #[cfg(test)]
                set_bcode(16, b_code);

                let err = if se_disjunct_hit {
                    FindErr::DisjunctConduct
                } else {
                    FindErr::OnlyKeyMatches
                };

                return Err(err);
            }

            #[cfg(test)]
            set_bcode(32, b_code);
            return Ok(find);
        }

        let mut extender = Extender {
            b: buff,
            f: &mut find,
            n: max_n,
            nl: min_ml,
            xl: max_ml,
        };

        if can_extend {
            let l = unsafe { links.unwrap_unchecked() };
            for (c, node) in l {
                if extender.e(node, *c) {
                    #[cfg(test)]
                    set_bcode(128, b_code);
                    return Ok(find);
                }
            }
        }

        if can_branch {
            let mut b = branching.iter();

            for (blinks, blen) in b.next_back() {
                let blen = *blen;
                if blen > max_ml {
                    continue;
                }

                extender.b.truncate(blen);

                let blinks = unsafe { blinks.as_ref().unwrap_unchecked() };

                for (&c, node) in blinks.iter() {
                    if skip_n == node as *const Node {
                        // happens only at topmost branching node
                        continue;
                    }

                    if extender.e(node, c) {
                        #[cfg(test)]
                        set_bcode(256, b_code);
                        return Ok(find);
                    }
                }
            }
        }

        #[cfg(test)]
        set_bcode(512, b_code);

        return if find.len() == 0 {
            Err(FindErr::DisjunctConduct)
        } else {
            Ok(find)
        };

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

    /// Use to clear entire tree.
    ///
    /// Return value is count of entries before clearing.
    pub fn cr(&mut self) -> usize {
        self.root = Node::empty();

        let cnt = self.cnt;
        self.cnt = 0;
        cnt
    }

    /// Use to extract entries from tree.
    ///
    /// Extraction is alphabetically unordered. Leaves tree intact.
    ///
    /// Return value is `None` for empty `Poetrie`.
    pub fn et(&mut self) -> Option<Vec<String>> {
        if self.cnt == 0 {
            return None;
        }

        // capacity is prebuffered to 1000
        let mut buff = Vec::with_capacity(1000);

        // capacity is prebuffered to 5000
        let mut res = Vec::with_capacity(5000);

        let rl = unsafe { self.root.links.as_ref().unwrap_unchecked() };
        extract(rl, &mut buff, &mut res);

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
    /// Conduct configuration prevents match.
    DisjunctConduct,
}

#[cfg_attr(test, derive(PartialEq))]
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

        pub fn rev(s: &str) -> String {
            s.chars().rev().collect()
        }

        #[derive(PartialEq, Debug)]
        pub struct RevEntry(pub String);

        impl RevEntry {
            pub fn new(e: &str) -> Self {
                let rev = rev(e);
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

        mod tests_of_units {
            use super::{RevEntry, rev};
            use crate::Entry;

            #[test]
            fn new() {
                let proof = RevEntry(String::from("abcd"));
                let test = RevEntry::new("dcba");
                assert_eq!(proof, test);
            }

            #[test]
            fn entry() {
                let proof = Entry("abcd");
                let test = RevEntry::new("dcba");
                assert_eq!(proof, test.entry());
            }

            #[test]
            fn _rev() {
                let proof = String::from("abcd");
                let test = rev("dcba");
                assert_eq!(proof, test);
            }

            #[test]
            fn deref() {
                let proof = String::from("abcd");
                let test = rev("dcba");
                assert_eq!(proof, *test);
            }
        }
    }

    mod get_node {
        use crate::{Links, Node, get_node};

        #[test]
        fn direct_return() {
            let mut l = Links::new();
            let c = 'a';
            let mut ecode = 0;

            _ = l.insert(c.clone(), Node::empty());

            let res = get_node(&l, &c, &mut ecode);
            assert_eq!(true, res.is_some());
            assert_eq!(1, ecode);
        }

        #[test]
        fn uppercasing() {
            let mut l = Links::new();
            let mut ecode = 0;

            _ = l.insert('A', Node::empty());

            let res = get_node(&l, &'a', &mut ecode);
            assert_eq!(true, res.is_some());
            assert_eq!(34, ecode);
        }

        #[test]
        fn lowercasing() {
            let mut l = Links::new();
            let mut ecode = 0;

            _ = l.insert('a', Node::empty());

            let res = get_node(&l, &'A', &mut ecode);
            assert_eq!(true, res.is_some());
            assert_eq!(36, ecode);
        }

        #[test]
        fn uncaseable() {
            let mut l = Links::new();
            let mut ecode = 0;

            _ = l.insert('-', Node::empty());

            let res = get_node(&l, &'_', &mut ecode);
            assert_eq!(true, res.is_none());
            assert_eq!(8, ecode);
        }

        #[test]
        fn not_one_to_one() {
            let mut l = Links::new();
            let c = 'ß';
            let mut ecode = 0;

            _ = l.insert('S', Node::empty());

            let res = get_node(&l, &c, &mut ecode);
            assert_eq!(true, res.is_none());
            assert_eq!(18, ecode);
        }

        #[test]
        fn not_match() {
            let mut l = Links::new();
            let mut ecode = 0;

            _ = l.insert('a', Node::empty());

            let res = get_node(&l, &'B', &mut ecode);
            assert_eq!(true, res.is_none());
            assert_eq!(36, ecode);
        }
    }

    mod extract {

        use crate::{Entry, Poetrie, extract};

        #[test]
        fn basic_test() {
            let mut poetrie = Poetrie::nw();

            let a = &Entry("a");
            let z = &Entry("z");

            _ = poetrie.it(a);
            _ = poetrie.it(z);

            let mut buff = Vec::new();
            let mut test = Vec::new();

            let links = poetrie.root.links.as_mut().unwrap();
            extract(links, &mut buff, &mut test);

            let proof = vec![String::from("a"), String::from("z")];
            assert_eq!(proof.len(), test.len());
            test.sort();

            assert_eq!(proof, test);

            assert_eq!(true, poetrie.ey(a));
            assert_eq!(true, poetrie.ey(z));
        }

        #[test]
        fn nesting() {
            let mut poetrie = Poetrie::nw();

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
                _ = poetrie.it(&Entry(e.as_str()));
            }

            let mut buff = Vec::new();
            let mut test = Vec::new();

            let links = poetrie.root.links.as_mut().unwrap();
            extract(links, &mut buff, &mut test);

            assert_eq!(entries.len(), test.len());

            test.sort();
            assert_eq!(entries, test);
        }

        #[test]
        fn in_depth_recursion() {
            let mut poetrie = Poetrie::nw();

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
                _ = poetrie.it(&Entry(p.as_str()));
            }

            let mut buff = Vec::new();
            let mut test = Vec::new();

            let links = poetrie.root.links.as_mut().unwrap();
            extract(links, &mut buff, &mut test);

            assert_eq!(paths.len(), test.len());

            test.sort();
            assert_eq!(paths, test);
        }
    }

    mod extender {

        // segment
        mod seg {
            use crate::{Links, Node};

            pub fn add_linked<'a>(mut n: &'a mut Node, s: &[&str]) -> &'a mut Node {
                for s in s {
                    n = add_one(n, s, true);
                }

                n
            }

            pub fn add_rooted<'a>(n: &'a mut Node, s: &[&str]) {
                for s in s {
                    _ = add_one(n, s, true);
                }
            }

            pub fn add_one<'a>(mut n: &'a mut Node, s: &str, e: bool) -> &'a mut Node {
                for c in s.chars() {
                    let l = n.links.get_or_insert(Links::new());

                    let e = l.entry(c);
                    n = e.or_insert(Node::empty());
                }

                n.entry = e;
                n
            }

            mod tests_of_units {
                use super::*;
                use crate::Node;

                fn as_usize(n: &Node) -> usize {
                    n as *const Node as usize
                }

                #[test]
                fn _add_linked() {
                    let mut n = Node::empty();
                    let res = as_usize(add_linked(&mut n, &["a", "b"]));

                    let mut n = &n;
                    for c in "ab".chars() {
                        let links = n.links.as_ref().unwrap();
                        n = links.get(&c).unwrap();

                        assert_eq!(true, n.entry);
                    }

                    assert_eq!(as_usize(n), res);
                }

                #[test]
                fn _add_rooted() {
                    let n = &mut Node::empty();
                    add_rooted(n, &["a", "b"]);

                    let links = n.links.as_ref().unwrap();
                    for c in "ab".chars() {
                        let n = links.get(&c).unwrap();
                        assert_eq!(true, n.entry);
                    }
                }

                #[test]
                fn _add_one_a() {
                    let n = &mut Node::empty();

                    let a1 = as_usize(add_one(n, "a", true));
                    let l = n.links.as_ref().unwrap();

                    one_test(a1, l, 'a', true);

                    let b1 = as_usize(add_one(n, "b", false));
                    let l = n.links.as_ref().unwrap();

                    one_test(b1, l, 'b', false);

                    assert_eq!(true, l.get(&'a').is_some());

                    fn one_test(res: usize, l: &Links, key: char, e: bool) {
                        let test = l.get(&key).unwrap();
                        assert_eq!(e, test.entry);
                        assert_eq!(false, test.links());
                        assert_eq!(res, as_usize(test));
                    }
                }

                #[test]
                fn _add_one_b() {
                    let mut root = Node::empty();

                    let seg = "ab";
                    let b = as_usize(add_one(&mut root, seg, true));

                    let mut n = &root;
                    for c in seg.chars() {
                        let l = n.links.as_ref().unwrap();
                        n = l.get(&c).unwrap();
                    }

                    assert_eq!(b, as_usize(n));

                    let seg = "ac";
                    let c = as_usize(add_one(&mut root, seg, true));

                    let mut l = root.links.as_ref().unwrap();
                    let a = l.get(&'a').unwrap();
                    assert_eq!(false, a.entry);
                    l = a.links.as_ref().unwrap();
                    assert_eq!(true, l.get(&'b').is_some());
                    assert_eq!(c, as_usize(l.get(&'c').unwrap()));
                }
            }
        }

        use seg::*;
        use std::collections::HashSet;

        use crate::{Extender, Find, Node, WordBuf, tests_of_units::rev_entry::rev};

        fn basic_ext<'a>(b: &'a mut WordBuf, f: &'a mut Find, n: usize) -> Extender<'a> {
            Extender {
                b,
                f,
                n,
                nl: 0,
                xl: usize::MAX,
            }
        }

        #[test]
        fn basic_test() {
            let mut f = Vec::new();
            let mut b: WordBuf = "end".chars().collect();

            let mut n = Node::empty();
            add_linked(&mut n, &["rse", "ment"]);

            let mut extender = basic_ext(&mut b, &mut f, usize::MAX);
            _ = extender.e(&n, 'o');

            assert_eq!(2, f.len());

            let p = ["endorse", "endorsement"].map(|x| rev(x));
            assert_eq!(p[0], f[0]);
            assert_eq!(p[1], f[1]);
        }

        #[test]
        fn immediate_saturation() {
            let mut f = Vec::new();
            let mut b = Vec::new();

            let mut n = Node::empty();
            n.entry = true;

            let mut extender = basic_ext(&mut b, &mut f, 1);

            _ = extender.e(&n, 'o');

            assert_eq!(1, f.len());
            assert_eq!(String::from('o'), f[0]);
            assert_eq!(vec!['o'], b);
        }

        #[test]
        #[should_panic(expected = "Caller disobeys precondition.")]
        fn invalid_buffer_length() {
            let mut f = Vec::new();
            let mut b = Vec::new();

            let mut extender = basic_ext(&mut b, &mut f, usize::MAX);
            extender.xl = 0;

            _ = extender.e(&Node::empty(), 'o');
        }

        #[test]
        fn match_limit_1() {
            let mut f = Vec::new();
            let mut b = "en".chars().collect();

            let mut n = Node::empty();
            n.entry = true;

            _ = add_one(&mut n, "orse", true);

            let mut extender = basic_ext(&mut b, &mut f, 2);

            let lim = extender.e(&n, 'd');
            assert_eq!(true, lim);

            assert_eq!(2, f.len());

            let pb = "endorse";
            let p = ["end", pb].map(|x| rev(x));
            assert_eq!(p[0], f[0]);
            assert_eq!(p[1], f[1]);

            assert_eq!(pb, b.iter().collect::<String>().as_str());
        }

        #[test]
        fn match_limit_2() {
            let outset = "en";

            let mut f = Vec::new();
            let mut b = outset.chars().collect();

            let mut n = Node::empty();
            n.entry = true;

            _ = add_one(&mut n, "orse", true);
            let mut extender = basic_ext(&mut b, &mut f, 3);
            let lim = extender.e(&n, 'd');
            assert_eq!(false, lim);

            assert_eq!(2, f.len());
            let p = ["end", "endorse"].map(|x| rev(x));
            assert_eq!(p[0], f[0]);
            assert_eq!(p[1], f[1]);

            assert_eq!(outset, b.iter().collect::<String>().as_str());
        }

        #[test]
        fn length_limits() {
            let outset = "do";

            let mut f = Vec::new();
            let mut b = outset.chars().collect();

            let mut n = Node::empty();

            let mut document = add_one(&mut n, "ument", true);
            let mut documental = add_one(&mut document, "al", true);
            _ = add_one(&mut documental, "ist", true);
            _ = add_one(&mut document, "able", true);

            let mut extender = Extender {
                b: &mut b,
                f: &mut f,
                n: 4,
                nl: "document".len() + 1,
                xl: "documentalist".len() - 1,
            };

            let res = extender.e(&mut n, 'c');
            assert_eq!(false, res);
            let mut proof = vec![rev("documental"), rev("documentable")];
            proof.sort();
            f.sort();
            assert_eq!(proof, f);
        }

        fn load_setup() -> (Node, HashSet<String>) {
            let mut n = Node::empty();

            _ = add_one(&mut n, "sity", true);

            let mut n_serot = add_one(&mut n, "t", false);
            add_rooted(&mut n_serot, &["axonomy", "herapy"]);

            let mut n_serotin = add_one(&mut n_serot, "in", false);
            add_rooted(&mut n_serotin, &["al", "e", "ous", "y"]);

            let mut n_seroton = add_one(&mut n_serot, "on", false);
            add_rooted(&mut n_seroton, &["ergic", "in"]);

            let proof = [
                "serosity",
                "serotaxonomy",
                "serotherapy",
                "serotinal",
                "serotine",
                "serotinous",
                "serotiny",
                "serotonergic",
                "serotonin",
            ]
            .map(|x| rev(x))
            .into_iter()
            .collect::<HashSet<String>>();

            (n, proof)
        }

        #[test]
        fn load_bearing_1() {
            let mut f = Vec::new();
            let mut b = "ser".chars().collect();

            let (n, p) = load_setup();

            let mut extender = basic_ext(&mut b, &mut f, usize::MAX);
            _ = extender.e(&n, 'o');

            assert_eq!(p.len(), f.len());
            for f in f {
                assert_eq!(true, p.contains(&f), "{f}");
            }
        }

        #[test]
        fn load_bearing_2() {
            let mut f = Vec::new();
            let mut b = "ser".chars().collect();

            let (n, p) = load_setup();

            let serotiny_len = "serotiny".len();
            let serotonergic_len = "serotonergic".len();

            let p = p
                .into_iter()
                .filter(|x| {
                    let l = x.len();
                    serotiny_len < l && l < serotonergic_len
                })
                .collect::<HashSet<String>>();

            let mut extender = Extender {
                b: &mut b,
                f: &mut f,
                n: usize::MAX,
                nl: serotiny_len + 1,
                xl: serotonergic_len - 1,
            };

            _ = extender.e(&n, 'o');

            assert_eq!(p.len(), f.len(), "{:?}, {:?}", f, p);

            for f in f {
                assert_eq!(true, p.contains(&f), "{f}");
            }
        }
    }

    mod push_match {
        use crate::{WordBuf, push_match};

        #[test]
        fn limit_hit_1() {
            let proof = "poetship";
            let cs = proof.chars().rev().collect::<WordBuf>();
            let mut f = Vec::new();

            let lim = push_match(&cs, &mut f, 2);
            assert_eq!(false, lim);
            assert_eq!(1, f.len());
            assert_eq!(proof, f[0]);
        }

        #[test]
        fn limit_hit_2() {
            let proof = "poet-cruiser";
            let cs = proof.chars().rev().collect::<WordBuf>();
            let mut f = Vec::new();
            f.push(String::with_capacity(0));

            let lim = push_match(&cs, &mut f, 2);
            assert_eq!(true, lim);
            assert_eq!(2, f.len());
            assert_eq!(proof, f[1]);
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

    mod mc_defaults {
        use crate::mc_defaults;

        #[test]
        fn constants() {
            assert_eq!(mc_defaults::MAX_N, 1);
            assert_eq!(mc_defaults::MIN_SL, 1);
            assert_eq!(mc_defaults::MAX_SL, usize::MAX);
            assert_eq!(mc_defaults::EXT_ML, 0);
            assert_eq!(mc_defaults::MAX_ML, usize::MAX);
            assert_eq!(mc_defaults::SUB_E, false);
        }
    }

    mod match_conduct {
        use crate::{MatchConduct, mc_defaults};

        mod new {
            use crate::{MatchConduct, mc_defaults};

            #[test]
            fn basic_test() {
                let mc =
                    MatchConduct::new(Some(10), Some(11), Some(12), Some(2), Some(14), Some(true))
                        .unwrap();
                assert_eq!(10, mc.max_n);
                assert_eq!(11, mc.min_sl);
                assert_eq!(12, mc.max_sl);
                assert_eq!(13, mc.min_ml);
                assert_eq!(14, mc.max_ml);
                assert_eq!(true, mc.sub_e);
                assert_ne!(mc_defaults::SUB_E, mc.sub_e);
            }

            #[test]
            fn validation() {
                let err = MatchConduct::new(Some(0), None, None, None, None, None);
                assert_eq!(true, err.is_err());
            }

            #[test]
            fn defaults() {
                let mc = MatchConduct::new(None, None, None, None, None, None).unwrap();
                assert_eq!(MatchConduct::default(), mc);
            }
        }

        #[test]
        fn default() {
            let mc = MatchConduct::default();

            assert_eq!(mc_defaults::MAX_N, mc.max_n);
            assert_eq!(mc_defaults::MIN_SL, mc.min_sl);
            assert_eq!(mc_defaults::MAX_SL, mc.max_sl);
            assert_eq!(mc_defaults::MIN_SL + mc_defaults::EXT_ML, mc.min_ml);
            assert_eq!(mc_defaults::MAX_ML, mc.max_ml);
            assert_eq!(mc_defaults::SUB_E, mc.sub_e);
        }

        mod val {
            use crate::{MatchConduct, ReqErr};

            #[test]
            fn zero_n() {
                let mut mc = MatchConduct::default();
                mc.max_n = 0;

                let err = MatchConduct::val(&mc);
                assert_eq!(Some(ReqErr::ZeroMaxMatches), err);
            }

            #[test]
            fn zero_suffix_requirement() {
                let mut mc = MatchConduct::default();
                mc.min_sl = 0;

                let err = MatchConduct::val(&mc);
                assert_eq!(Some(ReqErr::ZeroMinSufLen), err);
            }

            #[test]
            fn suffix_min_greater_max() {
                let mut mc = MatchConduct::default();
                mc.min_sl = 1;
                mc.max_sl = 0;

                let err = MatchConduct::val(&mc);
                assert_eq!(Some(ReqErr::SufLenMaxLessThanMin), err);
            }

            #[test]
            fn suffix_min_equal_max() {
                let mut mc = MatchConduct::default();
                mc.min_sl = 1;
                mc.max_sl = 1;

                let none = MatchConduct::val(&mc);
                assert_eq!(None, none);
            }

            #[test]
            fn length_min_greater_max() {
                let mut mc = MatchConduct::default();
                mc.min_ml = 1;
                mc.max_ml = 0;

                let err = MatchConduct::val(&mc);
                assert_eq!(Some(ReqErr::MatchLenMaxLessThanMin), err);
            }

            #[test]
            fn length_min_equal_max() {
                let mut mc = MatchConduct::default();
                mc.min_ml = 1;
                mc.max_ml = 1;

                let none = MatchConduct::val(&mc);
                assert_eq!(None, none);
            }

            #[test]
            fn length_min_less_than_suffix_min() {
                let mut mc = MatchConduct::default();
                mc.min_ml = 1;
                mc.min_sl = 2;

                let err = MatchConduct::val(&mc);
                assert_eq!(Some(ReqErr::MatchLenMinLessThanSufLenMin), err);
            }

            #[test]
            fn length_max_less_than_suffix_max() {
                // alogrithmically not problem
                // even connotes with concept of unbound
                // suffix, usize::MAX, still can be understood
                // as miscofiguration, kept loose
                let mut mc = MatchConduct::default();
                mc.max_ml = 1;
                mc.max_sl = 2;

                let none = MatchConduct::val(&mc);
                assert_eq!(None, none);
            }

            #[test]
            fn suffix_max_less_than_length_max() {
                let mut mc = MatchConduct::default();
                mc.max_ml = 2;
                mc.max_sl = 1;

                let none = MatchConduct::val(&mc);
                assert_eq!(None, none);
            }
        }

        #[test]
        fn max_l() {
            let vals = [(100, 101), (101, 100)];

            let mut mc = MatchConduct::default();
            for v in vals {
                mc.max_sl = v.0;
                mc.max_ml = v.1;

                assert_eq!(100, mc.max_l());
            }
        }
    }

    mod with_match_conduct {
        use crate::{MatchConduct, MatchConductWith, mc_defaults};

        #[test]
        fn basic_test() {
            let mut with = MatchConductWith::init();
            _ = with
                .with_max_n(10)
                .with_min_sl(11)
                .with_max_sl(12)
                .with_ext_ml(2)
                .with_max_ml(14)
                .with_sub_e(true);

            let test = with.with();

            let proof = MatchConduct {
                max_n: 10,
                min_sl: 11,
                max_sl: 12,
                min_ml: 13,
                max_ml: 14,
                sub_e: true,
            };

            assert_ne!(mc_defaults::SUB_E, proof.sub_e);
            assert_eq!(Ok(proof), test);
        }

        #[test]
        fn default() {
            let with = MatchConductWith::init();

            assert_eq!(MatchConduct::default(), with.0);
        }

        #[test]
        fn validation() {
            let mut with = MatchConductWith::init();
            let err = with.with_max_n(0).with();

            assert_eq!(true, err.is_err());
        }
    }

    mod poetrie {
        use crate::{Node, Poetrie};

        #[test]
        fn nw() {
            let poetrie = Poetrie::nw();

            assert_eq!(Node::empty(), poetrie.root);
            assert_eq!(0, poetrie.cnt);

            test(&poetrie.btr);
            test(&poetrie.buf);
            test(&poetrie.bra);

            fn test<T>(buf: &Vec<T>) {
                assert_eq!(0, buf.len());
                assert_eq!(0, buf.capacity());
            }
        }

        mod it {
            use crate::{Entry, Poetrie};

            #[test]
            fn basic_test() {
                let entry = Entry("touchstone");

                let mut poetrie = Poetrie::nw();
                let res = poetrie.it(&entry);
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

                let mut poetrie = Poetrie::nw();

                let res = poetrie.it(existing);
                assert_eq!(true, res);
                assert_eq!(1, poetrie.cnt);

                let res = poetrie.it(new);
                assert_eq!(true, res);
                assert_eq!(2, poetrie.cnt);

                assert_eq!(true, poetrie.ey(existing));
                assert_eq!(true, poetrie.ey(new));
            }

            #[test]
            fn singular_entry() {
                let e = Entry("a");

                let mut poetrie = Poetrie::nw();
                let res = poetrie.it(&e);
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

                let mut poetrie = Poetrie::nw();
                let res = poetrie.it(&entry);
                assert_eq!(true, res);
                assert_eq!(1, poetrie.cnt);

                let res = poetrie.it(&entry);
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

        mod ey {

            use crate::{Entry, Poetrie};

            #[test]
            fn member() {
                let e = &Entry("Keyword");
                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e);

                let res = poetrie.ey(e);
                assert_eq!(true, res);
            }

            #[test]
            fn not_member() {
                let e = &Entry("Keyword");
                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e);

                for e in ["Key", "Opener"] {
                    let e = Entry(e);
                    let res = poetrie.ey(&e);
                    assert_eq!(false, res);
                }
            }
        }

        mod sx {
            use crate::{Entry, FindErr, MatchConduct, Poetrie};

            #[test]
            fn basic_test() {
                let mut poetrie = Poetrie::nw();

                let proof = String::from("quadriliteral");
                let entry = Entry(proof.as_str());
                _ = poetrie.it(&entry);

                let key = Entry("semiliteral");
                let mc = MatchConduct::default();
                let find = poetrie.sx(&key, &mc);

                assert_eq!(Ok(vec![proof]), find);
            }

            #[test]
            fn err() {
                let poetrie = Poetrie::nw();

                let key = Entry("semiliteral");
                let mc = MatchConduct::default();
                let res = poetrie.sx(&key, &mc);
                assert_eq!(Err(FindErr::EmptyTree), res);
            }

            #[test]
            fn stores_clearing() {
                let mut poetrie = Poetrie::nw();

                let entry = Entry("semiliteral");
                let key_entry = Entry("quadriliteral");
                _ = poetrie.it(&entry);
                _ = poetrie.it(&key_entry);

                assert_eq!(0, poetrie.buf.capacity());
                assert_eq!(0, poetrie.bra.capacity());

                let mc = MatchConduct::default();
                _ = poetrie.sx(&key_entry, &mc);
                assert_eq!(0, poetrie.buf.len());
                assert_eq!(0, poetrie.bra.len());

                assert_eq!(true, poetrie.buf.capacity() > 0);
                assert_eq!(true, poetrie.bra.capacity() > 0);
            }
        }

        use core::ptr;

        #[test]
        fn clr_f_buffers() {
            let poetrie = Poetrie::nw();

            let bra = poetrie.bra.get_mut();
            let buf = poetrie.buf.get_mut();

            bra.push((ptr::null(), 0));
            buf.push('\0');

            poetrie.clr_f_buffs();

            assert_eq!(0, bra.len());
            assert_eq!(0, buf.len());

            assert_eq!(true, 0 < bra.capacity());
            assert_eq!(true, 0 < buf.capacity());
        }

        mod re {
            use crate::{Entry, Poetrie};

            #[test]
            fn known_unknown() {
                let known = &Entry("safe-hideaway");
                let unknown = &Entry("grave-monition");

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(known);

                assert_eq!(false, poetrie.re(unknown));
                assert_eq!(0, poetrie.btr.len());
                assert_eq!(true, poetrie.btr.capacity() > 0);
                assert_eq!(1, poetrie.cnt);

                assert_eq!(true, poetrie.re(known));
                assert_eq!(0, poetrie.btr.len());
                assert_eq!(0, poetrie.cnt);
                assert_eq!(false, poetrie.ey(known));
            }
        }

        // node in path to entry being deleted cannot
        // be deleted if and only if participates in
        // path to another entry where path len varies 0…m
        mod re_actual {

            use super::super::rev_entry::RevEntry;
            use crate::{Entry, Poetrie};

            #[test]
            fn basic_test() {
                let entry = RevEntry::new("abcxyz");
                let entry = &entry.entry();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(entry);
                _ = poetrie.track(entry, true);

                poetrie.re_actual(&mut 0);
                assert_eq!(false, poetrie.ey(entry));
            }

            #[test]
            fn one_letter_a() {
                let entry = &Entry("a");

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(entry);
                _ = poetrie.track(entry, true);

                let mut esc_code = 0;
                poetrie.re_actual(&mut esc_code);
                assert_eq!(false, poetrie.ey(entry));
                assert_eq!(18, esc_code);
            }

            #[test]
            fn one_letter_b() {
                let entry1 = &Entry("a");
                let entry2 = &Entry("b");

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(entry1);
                _ = poetrie.it(entry2);
                _ = poetrie.track(entry1, true);

                let mut esc_code = 0;
                poetrie.re_actual(&mut esc_code);
                assert_eq!(false, poetrie.ey(entry1));
                assert_eq!(true, poetrie.ey(entry2));
                assert_eq!(6, esc_code);
            }

            #[test]
            fn one_letter_c() {
                let entry1 = &Entry("a");
                let entry2 = RevEntry::new("al");
                let entry2 = &entry2.entry();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(entry1);
                _ = poetrie.it(entry2);
                _ = poetrie.track(entry1, true);

                let mut esc_code = 0;
                poetrie.re_actual(&mut esc_code);
                assert_eq!(false, poetrie.ey(entry1));
                assert_eq!(true, poetrie.ey(entry2));
                assert_eq!(1, esc_code);
            }

            #[test]
            fn inner_entry() {
                let mut poetrie = Poetrie::nw();

                let outer = RevEntry::new("Keyword");
                let outer = &outer.entry();
                _ = poetrie.it(&outer);

                let inner = RevEntry::new("Key");
                let inner = &inner.entry();
                _ = poetrie.it(inner);

                let mut esc_code = 0;
                _ = poetrie.track(inner, true);

                poetrie.re_actual(&mut esc_code);
                assert_eq!(1, esc_code);

                assert_eq!(false, poetrie.ey(inner));
                assert_eq!(true, poetrie.ey(outer));
            }

            #[test]
            fn links_removal() {
                let entry = RevEntry::new("Keyword");
                let entry = &entry.entry();
                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(entry);

                let mut esc_code = 0;
                _ = poetrie.track(entry, true);
                poetrie.re_actual(&mut esc_code);
                assert_eq!(18, esc_code);

                assert_eq!(false, poetrie.ey(entry));
                assert_eq!(None, poetrie.root.links);
            }

            #[test]
            fn node_composing_path() {
                let dissimilar = RevEntry::new("Dissimilar");
                let dissimilar = &dissimilar.entry();
                let keyword = RevEntry::new("Keyword");
                let keyword = &keyword.entry();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(dissimilar);
                _ = poetrie.it(keyword);

                let mut esc_code = 0;
                _ = poetrie.track(keyword, true);
                poetrie.re_actual(&mut esc_code);
                assert_eq!(6, esc_code);

                assert_eq!(false, poetrie.ey(keyword));
                assert_eq!(true, poetrie.ey(dissimilar));
            }

            #[test]
            fn entry_under_entry() {
                let above = RevEntry::new("keyworder");
                let above = &above.entry();
                let under = RevEntry::new("keyworders");
                let under = &under.entry();
                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(above);
                _ = poetrie.it(under);

                let mut esc_code = 0;
                _ = poetrie.track(under, true);
                poetrie.re_actual(&mut esc_code);
                assert_eq!(10, esc_code);

                assert_eq!(false, poetrie.ey(under));
                assert_eq!(true, poetrie.ey(above));

                _ = poetrie.track(above, true);
                let btr = &poetrie.btr;
                let last = btr[btr.len() - 1];
                assert_eq!('r', last.0);
                let node = unsafe { last.1.as_ref() }.unwrap();
                assert_eq!(false, node.links());
            }
        }

        mod find {
            use crate::{
                Entry, FindErr, MatchConduct, Poetrie, mc_defaults::MAX_ML,
                tests_of_units::rev_entry::RevEntry,
            };

            #[test]
            fn basic_test() {
                let p = ["halieutics", "codecs"].map(|x| String::from(x));

                let mut poetrie = Poetrie::nw();
                for p in p.iter() {
                    let entry = Entry(p.as_str());
                    _ = poetrie.it(&entry);
                }

                let k = &Entry("lyrics");
                let mut mc = MatchConduct::default();
                mc.max_n = usize::MAX;

                let f = poetrie.find(k, &mc, &mut 0).ok().unwrap();

                assert_eq!(p.len(), f.len());
                for p in p {
                    assert_eq!(true, p == f[0] || p == f[1]);
                }
            }

            #[test]
            fn exactly_last_match_1a() {
                let e = &Entry("s");
                let k = &Entry("lyrics");

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e);

                let mut mc = MatchConduct::default();
                mc.sub_e = true;
                mc.max_n = 2;

                for duo in [(1, 1056), (MAX_ML, 40)] {
                    mc.max_ml = duo.0;

                    let mut b_code = 0;
                    let f = poetrie.find(k, &mc, &mut b_code);

                    poetrie.clr_f_buffs();

                    assert_eq!(Ok(vec![String::from("s")]), f, "{duo:?}");
                    assert_eq!(duo.1, b_code);
                }
            }

            #[test]
            fn exactly_last_match_1b() {
                let e = &Entry("s");
                let k = &Entry("lyrics");

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e);
                _ = poetrie.it(k);

                let mut mc = MatchConduct::default();
                mc.sub_e = true;
                mc.max_n = 2;

                for duo in [(1, 1056), (MAX_ML, 34)] {
                    mc.max_ml = duo.0;

                    let mut b_code = 0;
                    let f = poetrie.find(k, &mc, &mut b_code);

                    poetrie.clr_f_buffs();

                    assert_eq!(Ok(vec![String::from("s")]), f);
                    assert_eq!(duo.1, b_code);
                }
            }

            #[test]
            fn exactly_last_match_2a() {
                let p = "lyrics";
                let k = &Entry("s");

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&Entry(p));

                let mut mc = MatchConduct::default();

                for duo in [(1, 130), (usize::MAX, 514)] {
                    mc.max_n = duo.0;

                    let mut b_code = 0;
                    let f = poetrie.find(k, &mc, &mut b_code);

                    poetrie.clr_f_buffs();

                    let proof = vec![String::from(p)];
                    assert_eq!(Ok(proof), f);
                    assert_eq!(duo.1, b_code);
                }
            }

            #[test]
            fn exactly_last_match_2b() {
                let p = "lyrics";

                let k = &Entry("s");

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&Entry(p));
                _ = poetrie.it(k);

                let mut mc = MatchConduct::default();
                for duo in [(1, 130), (usize::MAX, 514)] {
                    mc.max_n = duo.0;

                    let mut b_code = 0;

                    let f = poetrie.find(k, &mc, &mut b_code);
                    poetrie.clr_f_buffs();

                    let proof = vec![String::from(p)];
                    assert_eq!(Ok(proof), f);
                    assert_eq!(duo.1, b_code);
                }
            }

            #[test]
            fn exactly_last_match_3() {
                let k = &Entry("s");

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(k);

                let mut mc = MatchConduct::default();
                for max_ml in [1, MAX_ML] {
                    mc.max_ml = max_ml;

                    let mut b_code = 0;
                    let f = poetrie.find(k, &mc, &mut b_code);

                    poetrie.clr_f_buffs();

                    assert_eq!(Err(FindErr::OnlyKeyMatches), f);
                    assert_eq!(18, b_code);
                }
            }

            #[test]
            fn exactly_last_match_4() {
                let e = &Entry("s");
                let k = &Entry("S");

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e);

                let mut mc = MatchConduct::default();
                for max_ml in [1, MAX_ML] {
                    mc.max_ml = max_ml;

                    let mut b_code = 0;
                    let f = poetrie.find(k, &mc, &mut b_code);

                    poetrie.clr_f_buffs();

                    assert_eq!(Err(FindErr::OnlyKeyMatches), f);
                    assert_eq!(18, b_code);
                }
            }

            #[test]
            fn no_data() {
                let k = &Entry("lyrics");
                let mc = MatchConduct::default();

                let poetrie = Poetrie::nw();

                let mut b_code = 0;
                let f = poetrie.find(k, &mc, &mut b_code);

                assert_eq!(Err(FindErr::EmptyTree), f);
                assert_eq!(0, b_code);
            }

            #[test]
            fn no_suffix_match() {
                let e = &Entry("epicalyx");
                let k = &Entry("lyrics");
                let mc = MatchConduct::default();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e);

                let mut b_code = 0;
                let f = poetrie.find(k, &mc, &mut b_code);

                assert_eq!(Err(FindErr::NoJointSuffix), f);
                assert_eq!(4, b_code);
            }

            #[test]
            fn key_matches_itself_only_1() {
                let itself = &Entry("lyrics");
                let mc = MatchConduct::default();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(itself);

                let mut b_code = 0;
                let f = poetrie.find(itself, &mc, &mut b_code);

                assert_eq!(Err(FindErr::OnlyKeyMatches), f);
                assert_eq!(18, b_code);
            }

            #[test]
            fn key_matches_itself_only_2() {
                let e = &Entry("lyRics");
                let k = &Entry("lyrics");
                let mc = MatchConduct::default();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e);

                let mut b_code = 0;
                let f = poetrie.find(k, &mc, &mut b_code);

                assert_eq!(Err(FindErr::OnlyKeyMatches), f);
                assert_eq!(18, b_code);
            }

            #[test]
            // different casing is eventually considered to be different word
            fn key_matches_itself_only_3() {
                let p = String::from("lyRics");
                let e = &Entry(p.as_str());
                let k = &Entry("lyrics");
                let mc = MatchConduct::default();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e);
                _ = poetrie.it(k);

                let mut b_code = 0;
                let f = poetrie.find(k, &mc, &mut b_code);

                assert_eq!(Ok(vec![p]), f);
                assert_eq!(258, b_code);
            }

            #[test]
            fn key_with_subentry_is_suffix_to_entry_1() {
                let se = RevEntry::new("document");
                let e = RevEntry::new("documentalist");
                let k = RevEntry::new("documental");

                let mut mc = MatchConduct::default();
                mc.sub_e = true;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());
                _ = poetrie.it(&e.entry());

                let p = Ok(vec![se.0, e.0]);
                for duo in [(2, 130), (usize::MAX, 514)] {
                    mc.max_n = duo.0;

                    let mut b_code = 0;
                    let f = poetrie.find(&k.entry(), &mc, &mut b_code);

                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, b_code);
                }
            }

            #[test]
            fn key_with_subentry_is_suffix_to_entry_2() {
                let se = RevEntry::new("document");
                let e = RevEntry::new("documentalist");

                let k = RevEntry::new("documental");
                let k = &k.entry();

                let mut mc = MatchConduct::default();
                mc.sub_e = true;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());
                _ = poetrie.it(&e.entry());
                _ = poetrie.it(k);

                let p = Ok(vec![se.0, e.0]);
                for duo in [(2, 130), (usize::MAX, 514)] {
                    mc.max_n = duo.0;

                    let mut b_code = 0;
                    let f = poetrie.find(k, &mc, &mut b_code);

                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, b_code);
                }
            }

            #[test]
            fn matches_subentries_a_1() {
                let se_a = RevEntry::new("document");
                let se_b = RevEntry::new("documental");

                let k = RevEntry::new("documentalist");
                let k = &k.entry();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se_a.entry());
                _ = poetrie.it(&se_b.entry());
                _ = poetrie.it(k);

                let mut mc = MatchConduct::default();
                mc.sub_e = true;

                let p = Ok(vec![se_a.0, se_b.0]);
                for duo in [(2, 64), (usize::MAX, 34)] {
                    mc.max_n = duo.0;

                    let mut b_code = 0;
                    let find = poetrie.find(k, &mc, &mut b_code);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, find);
                    assert_eq!(duo.1, b_code);
                }
            }

            #[test]
            fn matches_subentries_a_2() {
                let se_a = RevEntry::new("document");
                let se_b = RevEntry::new("documental");

                let k = RevEntry::new("documentalist");
                let k = &k.entry();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se_a.entry());
                _ = poetrie.it(&se_b.entry());

                let mut mc = MatchConduct::default();
                mc.sub_e = true;

                let p = Ok(vec![se_a.0, se_b.0]);
                for duo in [(2, 64), (usize::MAX, 40)] {
                    mc.max_n = duo.0;

                    let mut b_code = 0;
                    let find = poetrie.find(k, &mc, &mut b_code);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, find);
                    assert_eq!(duo.1, b_code);
                }
            }

            #[test]
            fn matches_subentries_b_1() {
                let p = String::from("m");
                let se = Entry(p.as_str());

                let k = &Entry("anagram");
                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se);
                _ = poetrie.it(k);

                let mut mc = MatchConduct::default();
                mc.sub_e = true;

                let p = Ok(vec![p]);
                for duo in [(1, 64), (usize::MAX, 34)] {
                    mc.max_n = duo.0;

                    let mut b_code = 0;
                    let f = poetrie.find(k, &mc, &mut b_code);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, b_code);
                }
            }

            #[test]
            fn matches_subentries_b_2() {
                let p = String::from("m");
                let se = Entry(p.as_str());

                let k = &Entry("anagram");
                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se);

                let mut mc = MatchConduct::default();
                mc.sub_e = true;

                let p = Ok(vec![p]);
                for duo in [(1, 64), (usize::MAX, 40)] {
                    mc.max_n = duo.0;

                    let mut b_code = 0;
                    let f = poetrie.find(k, &mc, &mut b_code);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, b_code);
                }
            }

            #[test]
            fn matches_subentries_c_1() {
                let p = String::from("-ode");
                let se = Entry(p.as_str());

                let k = &Entry("X-ode");
                let mut mc = MatchConduct::default();
                mc.sub_e = true;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se);
                _ = poetrie.it(&k);

                let p = Ok(vec![p]);
                for duo in [(1, 64), (usize::MAX, 34)] {
                    mc.max_n = duo.0;

                    let mut b_code = 0;
                    let f = poetrie.find(k, &mc, &mut b_code);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, b_code);
                }
            }

            #[test]
            fn matches_subentries_c_2() {
                let p = String::from("-ode");
                let se = Entry(p.as_str());

                let k = &Entry("X-ode");
                let mut mc = MatchConduct::default();
                mc.sub_e = true;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se);

                let p = Ok(vec![p]);
                for duo in [(1, 64), (usize::MAX, 40)] {
                    mc.max_n = duo.0;

                    let mut b_code = 0;
                    let f = poetrie.find(k, &mc, &mut b_code);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, b_code);
                }
            }

            #[test]
            fn must_not_recourse_to_root_branching_a_1() {
                let p = String::from("hilum");
                let e_a = Entry(p.as_str());
                let e_b = Entry("claybank");

                let k = &Entry("haulm");
                let mut mc = MatchConduct::default();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e_a);
                _ = poetrie.it(&e_b);
                _ = poetrie.it(k);

                let p = Ok(vec![p]);
                for duo in [(1, 258), (usize::MAX, 514)] {
                    mc.max_n = duo.0;

                    let mut b_code = 0;
                    let f = poetrie.find(k, &mc, &mut b_code);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, b_code);
                }
            }

            #[test]
            fn must_not_recourse_to_root_branching_a_2() {
                let p = String::from("hilum");
                let e_a = Entry(p.as_str());
                let e_b = Entry("claybank");

                let k = &Entry("haulm");
                let mut mc = MatchConduct::default();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e_a);
                _ = poetrie.it(&e_b);

                let p = Ok(vec![p]);
                for duo in [(1, 132), (usize::MAX, 516)] {
                    mc.max_n = duo.0;

                    let mut b_code = 0;
                    let f = poetrie.find(k, &mc, &mut b_code);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, b_code);
                }
            }

            #[test]
            fn must_not_recourse_to_root_branching_b() {
                let k = &Entry("lyrics");
                let e = &Entry("disarrangement");
                let mc = MatchConduct::default();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(k);
                _ = poetrie.it(e);

                let mut b_code = 0;
                let f = poetrie.find(k, &mc, &mut b_code);

                assert_eq!(Err(FindErr::OnlyKeyMatches), f);
                assert_eq!(18, b_code);
            }

            #[test]
            fn key_partially_shared_suffix_1a() {
                let proof = String::from("lyrics");
                let entry = &Entry(proof.as_str());

                let key = &Entry("athletics");
                let mc = MatchConduct::default();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(entry);

                let mut b_code = 0;
                let find = poetrie.find(key, &mc, &mut b_code);

                assert_eq!(Ok(vec![proof]), find);
                assert_eq!(132, b_code);
            }

            #[test]
            fn key_partially_shared_suffix_1b() {
                let proof = String::from("lyrics");
                let entry = &Entry(proof.as_str());

                let key = &Entry("carboniferous");
                let mc = MatchConduct::default();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(entry);

                let mut b_code = 0;
                let find = poetrie.find(key, &mc, &mut b_code);

                assert_eq!(Ok(vec![proof]), find);
                assert_eq!(132, b_code);
            }

            #[test]
            fn key_partially_shared_suffix_2a() {
                let proof = String::from("lyrics");
                let entry = &Entry(proof.as_str());

                let key = &Entry("athletics");
                let mc = MatchConduct::default();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(entry);
                _ = poetrie.it(key);

                let mut b_code = 0;
                let find = poetrie.find(key, &mc, &mut b_code);

                assert_eq!(Ok(vec![proof]), find);
                assert_eq!(258, b_code);
            }

            #[test]
            fn key_partially_shared_suffix_2b() {
                let proof = String::from("lyrics");
                let entry = &Entry(proof.as_str());

                let key = &Entry("carboniferous");
                let mc = MatchConduct::default();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(entry);
                _ = poetrie.it(key);

                let mut b_code = 0;
                let find = poetrie.find(key, &mc, &mut b_code);

                assert_eq!(Ok(vec![proof]), find);
                assert_eq!(258, b_code);
            }

            #[test]
            fn key_partially_shared_suffix_3a() {
                let proof = String::from("X-lyrics");
                let entry = &Entry(proof.as_str());

                let key = &Entry("A-lyrics");
                let mc = MatchConduct::default();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(entry);
                _ = poetrie.it(key);

                let mut b_code = 0;
                let find = poetrie.find(key, &mc, &mut b_code);

                assert_eq!(Ok(vec![proof]), find);
                assert_eq!(258, b_code);
            }

            #[test]
            fn key_partially_shared_suffix_3b() {
                let proof = String::from("X-lyrics");
                let entry = &Entry(proof.as_str());

                let key = &Entry("A-lyrics");
                let mc = MatchConduct::default();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(entry);

                let mut b_code = 0;
                let find = poetrie.find(key, &mc, &mut b_code);

                assert_eq!(Ok(vec![proof]), find);
                assert_eq!(132, b_code);
            }

            #[test]
            fn key_partially_shared_suffix_4a() {
                let proof_1 = String::from("lyrics");
                let entry_1 = &Entry(proof_1.as_str());

                let proof_2 = String::from("ethics");
                let entry_2 = &Entry(proof_2.as_str());

                let key = &Entry("athletics");
                let mc = MatchConduct::default();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(entry_1);
                _ = poetrie.it(entry_2);

                _ = poetrie.it(key);

                let mut b_code = 0;
                let find = poetrie.find(key, &mc, &mut b_code);

                assert_eq!(true, find.is_ok());
                let res = find.unwrap();

                assert_eq!(1, res.len());
                let find = &res[0];

                assert_eq!(258, b_code);

                let equal = &proof_1 == find || &proof_2 == find;

                assert_eq!(true, equal);
            }

            #[test]
            fn key_partially_shared_suffix_4b() {
                let proof_1 = String::from("lyrics");
                let entry_1 = &Entry(proof_1.as_str());

                let proof_2 = String::from("emphasis");
                let entry_2 = &Entry(proof_2.as_str());

                let key = &Entry("carboniferous");
                let mc = MatchConduct::default();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(entry_1);
                _ = poetrie.it(entry_2);

                _ = poetrie.it(key);

                let mut b_code = 0;
                let find = poetrie.find(key, &mc, &mut b_code);

                assert_eq!(true, find.is_ok());
                let res = find.unwrap();

                assert_eq!(1, res.len());
                let find = &res[0];

                assert_eq!(258, b_code);

                let equal = &proof_1 == find || &proof_2 == find;

                assert_eq!(true, equal);
            }

            #[test]
            fn case_ignoring() {
                let subentry = "DoCuMeNt";
                let entry = "DoCuMeNtAlIsT";

                let key = "dOcUmEnTaL";

                let proof1 = key[..subentry.len()].to_string();
                let proof2 = format!("{}{}", key, &entry[key.len()..]);

                let subentry = RevEntry::new(subentry);
                let entry = RevEntry::new(entry);

                let key = RevEntry::new(key);
                let mut mc = MatchConduct::default();
                mc.max_n = 2;
                mc.sub_e = true;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&subentry.entry());
                _ = poetrie.it(&entry.entry());

                let mut b_code = 0;
                let find = poetrie.find(&key.entry(), &mc, &mut b_code);

                let proof1 = RevEntry::new(proof1.as_str());
                let proof2 = RevEntry::new(proof2.as_str());

                assert_eq!(Ok(vec![proof1.0, proof2.0]), find);

                assert_eq!(130, b_code);
            }

            use crate::Find;
            #[test]
            fn load() {
                let mut poetrie = Poetrie::nw();

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
                    _ = poetrie.it(&Entry(e));
                }

                let key = Entry("musics");
                let proof = String::from("physics");
                assert(Ok(vec![proof]), 132, key, &poetrie, 1);

                let key = Entry("athletics");
                let proof = String::from("aesthetics");
                assert(Ok(vec![proof]), 258, key, &poetrie, 1);

                let key = Entry("aesthetics");
                let proof = String::from("athletics");
                assert(Ok(vec![proof]), 258, key, &poetrie, 1);

                let key = Entry("epicalyx");
                assert(Err(FindErr::NoJointSuffix), 4, key, &poetrie, 1);

                let key = RevEntry::new("documental");
                let proof1 = RevEntry::new("document").0;
                let proof2 = RevEntry::new("documentalist").0;
                assert(Ok(vec![proof1, proof2]), 130, key.entry(), &poetrie, 2);

                let key = RevEntry::new("documentalist");
                let proof = RevEntry::new("document").0;
                assert(Ok(vec![proof]), 34, key.entry(), &poetrie, 2);

                let key = RevEntry::new("quadriceps");
                let proof = String::from("q");
                assert(Ok(vec![proof]), 64, key.entry(), &poetrie, 1);

                let key = Entry("q");
                assert(Err(FindErr::OnlyKeyMatches), 18, key, &poetrie, 1);

                let key = Entry("epically");
                assert(Err(FindErr::OnlyKeyMatches), 18, key, &poetrie, 1);

                fn assert<'a>(
                    res: Result<Find, FindErr>,
                    code: usize,
                    key: crate::Key,
                    poetrie: &Poetrie,
                    n: usize,
                ) {
                    let mut mc = MatchConduct::default();
                    mc.max_n = n;
                    mc.sub_e = true;

                    let mut b_code = 0;
                    assert_eq!(
                        res,
                        poetrie.find(&key, &mc, &mut b_code),
                        "c: {}, bc: {}",
                        code,
                        b_code
                    );
                    assert_eq!(code, b_code);

                    poetrie.buf.get_mut().clear();
                    poetrie.bra.get_mut().clear();
                }
            }
        }

        mod track {

            use super::super::rev_entry::RevEntry;
            use crate::{NULL, Poetrie, TraRes};

            #[test]
            fn tracing() {
                let mut poetrie = Poetrie::nw();

                let keyword = "keyword";
                let entries = ["k", "key", keyword].map(|x| RevEntry::new(x));

                for e in entries.iter() {
                    _ = poetrie.it(&e.entry());
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

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(entry);
                let res = poetrie.track(entry, false);

                assert_eq!(TraRes::Ok, res);
            }

            #[test]
            fn unknown_not_path() {
                let entry = RevEntry::new("wordbook");
                let bad_entry = RevEntry::new("wordbooks");

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&entry.entry());
                let res = poetrie.track(&bad_entry.entry(), false);
                assert_eq!(TraRes::UnknownForAbsentPathLinks, res);
            }

            #[test]
            fn unknown_not_path_2() {
                let entry = RevEntry::new("wordbookz");
                let bad_entry = RevEntry::new("wordbooks");

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&entry.entry());
                let res = poetrie.track(&bad_entry.entry(), false);
                assert_eq!(TraRes::UnknownForAbsentPathNode, res);
            }

            #[test]
            fn unknown_not_entry() {
                let entry = RevEntry::new("wordbooks");
                let bad_entry = RevEntry::new("wordbook");

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&entry.entry());

                let res = poetrie.track(&bad_entry.entry(), false);
                assert_eq!(TraRes::UnknownForNotEntry, res);
            }
        }

        use crate::Entry;

        #[test]
        fn cr() {
            let keyentry = Entry("keyentry");
            let mut poetrie = Poetrie::nw();

            _ = poetrie.it(&keyentry);
            let cap = 50;
            poetrie.btr.get_mut().reserve(cap);
            poetrie.buf.get_mut().reserve(cap);

            assert_eq!(1, poetrie.cr());
            assert_eq!(false, poetrie.ey(&keyentry));
            let root = &poetrie.root;
            assert_eq!(false, root.links());
            assert_eq!(false, root.entry);
            assert_eq!(0, poetrie.cnt);

            assert_eq!(true, poetrie.btr.capacity() >= cap);
            assert_eq!(true, poetrie.buf.capacity() >= cap);
        }

        #[test]
        fn ct() {
            let test = 3;
            let mut poetrie = Poetrie::nw();
            assert_eq!(0, poetrie.ct());
            poetrie.cnt = test;
            assert_eq!(test, poetrie.ct());
        }

        mod et {
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

                let mut poetrie = Poetrie::nw();
                for e in entries.clone() {
                    _ = poetrie.it(&e);
                }

                let ext = poetrie.et();
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
                    assert_eq!(true, poetrie.ey(&e));
                }
            }

            #[test]
            fn empty_tree() {
                let mut poetrie = Poetrie::nw();
                let ext = poetrie.et();

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

    mod readme {
        use crate::{Entry, FindErr, MatchConduct, Poetrie};

        #[test]
        fn sample_1() {
            let mut poetrie = Poetrie::nw();
            let words = ["analytics", "metrics", "ethics", "Acoustics"]
                .map(|x| Entry::new_from_str(x).unwrap());
            for w in words {
                poetrie.it(&w);
            }

            let mc = MatchConduct::default();

            let probe = Entry::new_from_str("lyrics").unwrap();

            let matchee = poetrie.sx(&probe, &mc);
            assert_eq!(Ok(vec![String::from("metrics")]), matchee);

            let probe = Entry::new_from_str("solemn").unwrap();
            assert_eq!(Err(FindErr::NoJointSuffix), poetrie.sx(&probe, &mc));
        }

        #[test]
        fn sample_2() {
            let mut poetrie = Poetrie::nw();
            let words = ["lynx", "index"].map(|x| Entry::new_from_str(x).unwrap());
            for w in words {
                poetrie.it(&w);
            }

            let probe = Entry::new_from_str("ynx").unwrap();
            let mc = MatchConduct::default();
            let matchee = poetrie.sx(&probe, &mc);

            assert_eq!(Ok(vec![String::from("lynx")]), matchee);
        }
    }
}

// cargo fmt && cargo test --release
