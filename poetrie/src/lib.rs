//! Poetrie, poetic trie, is trie designated for finding rhymes for your verses.
//!
//! For given input, and populated tree, it will find words with shared suffix for you.

use std::{cmp::min, collections::hash_map::HashMap, ops::Deref};

mod aide;
mod uc;
use uc::UC;

type Links = HashMap<char, Node>;

/// Actual matches found type.
pub type Find = Vec<String>;

/// `char` buffer
type CharBuf = String;
/// branching information
type BraInf = Vec<(*const HashMap<char, Node>, usize, *const Node)>;
/// backtrace buffer
type BtrBuf = Vec<(char, *mut Node)>;

fn extract(l: &Links, buff: &mut CharBuf, o: &mut Vec<String>) {
    for (k, n) in l.iter() {
        buff.push(*k);

        if n.entry {
            let entry = buff.chars().rev().collect();
            o.push(entry);
        }

        if let Some(l) = n.links.as_ref() {
            extract(l, buff, o);
        }

        _ = buff.pop();
    }
}

struct Extender<'a> {
    b: &'a mut CharBuf,
    f: &'a mut Find,
    /// matches limit
    n: usize,
    /// max length
    xl: usize,
    /// min length
    nl: usize,
}

impl<'a> Extender<'a> {
    fn e(&mut self, n: &Node, c: char) -> bool {
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

fn push_match(c: &CharBuf, f: &mut Find, l: usize) -> bool {
    let e = c.chars().rev().collect();

    f.push(e);
    f.len() == l
}

/// [`Entry`] alias for using in key role.
pub type Key<'a> = Entry<'a>;

/// [`&str`] validated for usage with [`Poetrie`].
#[derive(Clone, PartialEq, Debug)]
pub struct Entry<'a>(&'a str);

impl<'a> Entry<'a> {
    /// Use to construct new `Entry` instance.
    ///
    /// Return value is [`None`] for 0-length [`str`].
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
    /// Suffix match is posed by at least one [`char`] match.
    ZeroMinSufLen,
    /// Maximal suffix match length cannot be less than minimal.
    SufLenMaxLessThanMin,
    /// Maximal match length cannot be less than minimal.
    MatchLenMaxLessThanMin,
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
    // extra match length requirement
    ext_ml: usize,
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
    /// Every parameter provided with [`None`] will use default as expressed at [`MatchConduct::default`].
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

        let new = Self {
            max_n,
            min_sl,
            max_sl,
            ext_ml,
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
            ext_ml: EXT_ML,
            max_ml: MAX_ML,
            sub_e: SUB_E,
        };

        #[cfg(test)]
        Self::val(&new);

        new
    }

    fn val(s: &Self) -> Option<ReqErr> {
        let min_sl = s.min_sl;

        let err = if s.max_n == 0 {
            ReqErr::ZeroMaxMatches
        } else if min_sl == 0 {
            ReqErr::ZeroMinSufLen
        } else if s.max_sl < min_sl {
            ReqErr::SufLenMaxLessThanMin
        } else if s.max_ml < s.min_ml() {
            ReqErr::MatchLenMaxLessThanMin
        } else {
            return None;
        };

        Some(err)
    }

    /// max operative suffix length
    fn max_o_sl(&self) -> usize {
        min(self.max_ml, self.max_sl)
    }

    const fn min_ml(&self) -> usize {
        self.min_sl + self.ext_ml
    }
}

/// Chain-of-adjustments refining type, [`MatchConduct`] configurator.
///
/// Use various methods provided to adjust [`MatchConduct`]
/// values as desired.
///
/// Check with [`MatchConduct::new`] for detailed explanation.
///
/// ```
/// use poetrie::{MatchConductShaper, MatchConduct};
///
/// let mut chain = MatchConductShaper::init();
/// _ = chain.max_n(10).max_ml(8);
///
/// let mc: MatchConduct = chain.form().unwrap();
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct MatchConductShaper(MatchConduct);

impl MatchConductShaper {
    /// Use to construct new `MatchConductShaper` instance.
    ///
    /// Constructed with [`MatchConduct::default()`] as initial value.
    ///
    /// Check with [`MatchConductShaper::form`] or [`MatchConductShaper::transform`]
    /// for more details.
    pub fn init() -> MatchConductShaper {
        Self(MatchConduct::default())
    }

    /// Use to adjust matches limit.
    pub fn max_n(&mut self, max_n: usize) -> &mut Self {
        self.0.max_n = max_n;
        self
    }

    /// Use to adjust minimal suffix match length.
    pub fn min_sl(&mut self, min_sl: usize) -> &mut Self {
        self.0.min_sl = min_sl;
        self
    }

    /// Use to adjust maximal suffix match length.
    pub fn max_sl(&mut self, max_sl: usize) -> &mut Self {
        self.0.max_sl = max_sl;
        self
    }

    /// Use to adjust extra match length requirement.
    pub fn ext_ml(&mut self, ext_ml: usize) -> &mut Self {
        self.0.ext_ml = ext_ml;
        self
    }

    /// Use to adjust maximal match length.
    pub fn max_ml(&mut self, max_ml: usize) -> &mut Self {
        self.0.max_ml = max_ml;
        self
    }

    /// Use to adjust sub-entries inclusion flag.
    pub fn sub_e(&mut self, sub_e: bool) -> &mut Self {
        self.0.sub_e = sub_e;
        self
    }

    /// Use to validate and obtain [`MatchConduct`] instance.
    ///
    /// Return value is [`Result`] with either valid [`MatchConduct`]
    /// instance or with [`ReqErr`] error information.
    pub fn form(&self) -> Result<MatchConduct, ReqErr> {
        if let Some(e) = MatchConduct::val(&self.0) {
            Err(e)
        } else {
            Ok(self.0.clone())
        }
    }

    /// Use to validate and obtain [`MatchConduct`] instance.
    ///
    /// Return value is [`Result`] with either valid [`MatchConduct`]
    /// instance or with [`ReqErr`] error information.
    pub fn transform(self) -> Result<MatchConduct, (ReqErr, Self)> {
        if let Some(e) = MatchConduct::val(&self.0) {
            Err((e, self))
        } else {
            Ok(self.0)
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
    btr: UC<BtrBuf>,
    // character buffer
    buf: UC<CharBuf>,
    // branching information
    bra: UC<BraInf>,
    // entries count
    cnt: usize,
}

#[cfg(test)]
use crate::tests_of_units::poetrie::find::grade;

const NULL: char = '\0';
impl Poetrie {
    /// Use for `Poetrie` construction.
    pub fn nw() -> Poetrie {
        Poetrie {
            root: Node::empty(),
            btr: UC::new(BtrBuf::new()),
            buf: UC::new(CharBuf::new()),
            bra: UC::new(BraInf::new()),
            cnt: 0,
        }
    }

    /// Use for entry insertions into tree.
    ///
    /// Return value is [`true`] if entry was inserted into tree,
    /// [`false`] if it was present already.
    pub fn it(&mut self, entry: &Entry) -> bool {
        let mut node = &mut self.root;
        let mut chars = entry.chars();
        while let Some(c) = chars.next_back() {
            let links = node.links.get_or_insert_with(|| Links::new());
            node = links.entry(c).or_insert(Node::empty());

            #[cfg(test)]
            {
                node.c = c;
            }
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
    /// Return value is [`true`] if entry is present in tree, [`false`] otherwise.
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
    /// By obvious means minimal suffix match length is 1 [`char`].
    ///
    /// Use `mc` to express matching behavior adjustments. Check with [`MatchConduct::new()`]
    /// or [`MatchConductShaper`] for details.
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
    /// use poetrie::{MatchConductShaper, MatchConduct};
    ///
    /// let mut shaper = MatchConductShaper::init();
    /// shaper
    ///    .min_sl(3).max_sl(5).ext_ml(1)
    ///    .max_ml(10).sub_e(false).max_n(15);
    ///
    /// let mc: MatchConduct = shaper.form().unwrap();
    /// ```
    pub fn sx(&self, key: &Key, mc: &MatchConduct) -> Result<Find, FindErr> {
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
        self.bra.promote().clear();
        self.buf.promote().clear();
    }

    /// Use to remove entry from tree.
    ///
    /// Return value is [`true`] if entry was removed, [`false`] if it was not present.
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

        self.btr.clear();
        res
    }

    fn re_actual(&mut self, #[cfg(test)] grade: &mut usize) {
        let mut trace = self.btr.iter();
        let en_duo = unsafe { trace.next_back().unwrap_unchecked() };
        let mut node = unsafe { en_duo.1.as_mut().unwrap_unchecked() };

        node.entry = false;
        if node.links() {
            #[cfg(test)]
            set_grade(1, grade);

            return;
        }

        // subnode entry
        let mut sn_entry = &en_duo.0;
        while let Some((c, n)) = trace.next_back() {
            node = unsafe { n.as_mut().unwrap_unchecked() };
            let links = unsafe { node.links.as_mut().unwrap_unchecked() };
            _ = links.remove(sn_entry);

            #[cfg(test)]
            set_grade(2, grade);

            if links.len() > 0 {
                #[cfg(test)]
                set_grade(4, grade);

                return;
            }

            if node.entry {
                #[cfg(test)]
                set_grade(8, grade);

                break;
            }

            sn_entry = c;
        }

        node.links = None;
        #[cfg(test)]
        if *grade != (2 | 8) {
            set_grade(16, grade);
        }

        #[cfg(test)]
        fn set_grade(g: usize, grade_ref: &mut usize) {
            let grade = *grade_ref;
            *grade_ref = grade | g;
        }
    }

    fn find(
        &self,
        key: &Key,
        mc: &MatchConduct,
        #[cfg(test)] grade: &mut usize,
    ) -> Result<Find, FindErr> {
        #[cfg(test)]
        assert_eq!(true, MatchConduct::val(mc).is_none());

        // operative node
        let mut op_node = &self.root;

        let mut chars = key.chars();
        let mut c = unsafe { chars.next_back().unwrap_unchecked() };

        if let Some(l) = op_node.links.as_ref() {
            if let Some(n) = l.get(&c) {
                op_node = n;
            } else {
                return Err(FindErr::NoJointSuffix);
            }
        } else {
            return Err(FindErr::EmptyTree);
        }

        let max_n = mc.max_n;
        let max_o_sl = mc.max_o_sl();

        let min_sl = mc.min_sl;
        let min_ml = mc.min_ml();
        let max_ml = mc.max_ml;

        let sub_e = mc.sub_e;

        let branching = self.bra.promote();
        let mut disjunct_hit = false;

        let mut find = Vec::with_capacity(100);

        let buff = self.buf.promote();
        let mut buf_l;
        let mut max_l_accord;

        'track: loop {
            // devnote: can be guarded by inspection
            // so heap push is avoided, needs some counter
            // instead
            buff.push(c);
            buf_l = buff.len();

            // unwinding key, instead of short-cutting,
            // is necessary for disjunct conduct determination
            max_l_accord = buf_l <= max_o_sl;

            let next_c = chars.next_back();
            if next_c.is_none() {
                #[cfg(test)]
                set_grade(grade::KEY_EXH, grade);
                break 'track;
            }

            if op_node.entry {
                if sub_e && max_l_accord && min_ml <= buf_l {
                    if push_match(buff, &mut find, max_n) {
                        #[cfg(test)]
                        set_grade(grade::SAT_ON_SE, grade);
                        return Ok(find);
                    }
                } else {
                    disjunct_hit = true;
                }
            }

            if let Some(l) = op_node.links.as_ref() {
                c = unsafe { next_c.unwrap_unchecked() };
                if let Some(n) = l.get(&c) {
                    if l.len() > 1 {
                        if max_l_accord && min_sl <= buf_l {
                            branching.push((l, buf_l, n));
                        } else {
                            disjunct_hit = true;
                        }
                    }

                    op_node = n;
                    continue;
                }

                #[cfg(test)]
                set_grade(grade::NO_PATH_N, grade);
                break 'track;
            }

            #[cfg(test)]
            set_grade(grade::NO_PATH_L, grade);
            break 'track;
        }

        if buf_l < min_sl {
            #[cfg(test)]
            set_grade(grade::MIN_SL_NOT_REA, grade);
            return Err(FindErr::DisjunctConduct);
        }

        let links = op_node.links.as_ref();
        let continuable = links.is_some();

        // extension is special case of branching where
        // branching node is last node of key
        let can_extend = max_l_accord && continuable && buf_l < max_ml;
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
                set_grade(grade::G_ZERO_M, grade);

                let err = if disjunct_hit || continuable {
                    FindErr::DisjunctConduct
                } else {
                    FindErr::OnlyKeyMatches
                };

                return Err(err);
            }

            #[cfg(test)]
            set_grade(grade::SUB_E_ONLY, grade);
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
                    set_grade(grade::SAT_ON_EXT, grade);
                    return Ok(find);
                }
            }
        }

        if can_branch {
            let mut b = branching.iter();

            while let Some((blinks, blen, skip_n)) = b.next_back() {
                let blen = *blen;
                if blen == max_ml {
                    // `==` occurs when buf_l = max_l = max_ml
                    // it is simpler to skip already long enough buffer here
                    // than checking each time for both conditions,
                    // buf_l <= max_sl && buf_l < max_ml, instead of buf_l <= max_l
                    #[cfg(test)]
                    set_grade(grade::BUF_MAX_ALR, grade);
                    continue;
                }

                extender.b.truncate(blen);

                // devnote: check with option to avoid raw pointers
                let blinks = unsafe { blinks.as_ref().unwrap_unchecked() };

                for (c, node) in blinks.iter() {
                    if node as *const Node == *skip_n {
                        continue;
                    }

                    if extender.e(node, *c) {
                        #[cfg(test)]
                        set_grade(grade::SAT_ON_BRA, grade);
                        return Ok(find);
                    }
                }
            }
        }

        #[cfg(test)]
        set_grade(grade::FIN, grade);

        return if find.len() == 0 {
            Err(FindErr::DisjunctConduct)
        } else {
            Ok(find)
        };

        #[cfg(test)]
        fn set_grade(g: usize, grade_ref: &mut usize) {
            let grade = *grade_ref;
            *grade_ref = grade | g;
        }
    }

    fn track(&self, entry: &Key, trace: bool) -> TraRes {
        let mut node = &self.root;
        let btr = self.btr.promote();

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
    /// Return value is [`None`] for empty `Poetrie`.
    pub fn et(&mut self) -> Option<Vec<String>> {
        let cnt = self.cnt;
        if cnt == 0 {
            return None;
        }

        let buff = self.buf.aq_mut();
        let mut res = Vec::with_capacity(cnt);

        let rl = unsafe { self.root.links.as_ref().unwrap_unchecked() };
        extract(rl, buff, &mut res);

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
    #[cfg(test)]
    c: char,
    links: Option<Links>,
    entry: bool,
}

impl Node {
    const fn links(&self) -> bool {
        self.links.is_some()
    }

    const fn empty() -> Self {
        Node {
            #[cfg(test)]
            c: '\0',
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

    use crate::MatchConduct;
    impl MatchConduct {
        fn test() -> Self {
            let new = Self {
                max_n: 1,
                min_sl: 1,
                max_sl: usize::MAX,
                ext_ml: 0,
                max_ml: usize::MAX,
                sub_e: false,
            };

            Self::val(&new);

            new
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

            let mut buff = String::new();
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

            let mut buff = String::new();
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
                String::from("bycd"),
                String::from("bycdefgh"),
                String::from("byceff"),
                String::from("byceffgq"),
                String::from("bycqff"),
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

            let mut buff = String::new();
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
                use crate::aide::address;

                #[test]
                fn _add_linked() {
                    let mut n = Node::empty();
                    let res = address(add_linked(&mut n, &["a", "b"]));

                    let mut n = &n;
                    for c in "ab".chars() {
                        let links = n.links.as_ref().unwrap();
                        n = links.get(&c).unwrap();

                        assert_eq!(true, n.entry);
                    }

                    assert_eq!(address(n), res);
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

                    let a1 = address(add_one(n, "a", true));
                    let l = n.links.as_ref().unwrap();

                    one_test(a1, l, 'a', true);

                    let b1 = address(add_one(n, "b", false));
                    let l = n.links.as_ref().unwrap();

                    one_test(b1, l, 'b', false);

                    assert_eq!(true, l.get(&'a').is_some());

                    fn one_test(res: usize, l: &Links, key: char, e: bool) {
                        let test = l.get(&key).unwrap();
                        assert_eq!(e, test.entry);
                        assert_eq!(false, test.links());
                        assert_eq!(res, address(test));
                    }
                }

                #[test]
                fn _add_one_b() {
                    let mut root = Node::empty();

                    let seg = "ab";
                    let b = address(add_one(&mut root, seg, true));

                    let mut n = &root;
                    for c in seg.chars() {
                        let l = n.links.as_ref().unwrap();
                        n = l.get(&c).unwrap();
                    }

                    assert_eq!(b, address(n));

                    let seg = "ac";
                    let c = address(add_one(&mut root, seg, true));

                    let mut l = root.links.as_ref().unwrap();
                    let a = l.get(&'a').unwrap();
                    assert_eq!(false, a.entry);
                    l = a.links.as_ref().unwrap();
                    assert_eq!(true, l.get(&'b').is_some());
                    assert_eq!(c, address(l.get(&'c').unwrap()));
                }
            }
        }

        use seg::*;
        use std::collections::HashSet;

        use crate::{CharBuf, Extender, Find, Node, tests_of_units::rev_entry::rev};

        fn basic_ext<'a>(b: &'a mut CharBuf, f: &'a mut Find, n: usize) -> Extender<'a> {
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
            let mut b: CharBuf = String::from("end");

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
            let mut b = String::new();

            let mut n = Node::empty();
            n.entry = true;
            _ = add_one(&mut n, "leaster", true);

            let mut extender = basic_ext(&mut b, &mut f, 1);

            _ = extender.e(&n, 'o');

            let proof = String::from('o');
            assert_eq!(1, f.len());
            assert_eq!(proof, f[0]);
            assert_eq!(proof, b);
        }

        #[test]
        #[should_panic(expected = "Caller disobeys precondition.")]
        fn invalid_buffer_length() {
            let mut f = Vec::new();
            let mut b = String::new();

            let mut extender = basic_ext(&mut b, &mut f, usize::MAX);
            extender.xl = 0;

            _ = extender.e(&Node::empty(), 'o');
        }

        #[test]
        fn match_limit_a() {
            let mut f = Vec::new();
            let mut b = String::from("en");

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

            assert_eq!(pb, b.as_str());
        }

        #[test]
        fn match_limit_b() {
            let outset = "en";

            let mut f = Vec::new();
            let mut b = String::from(outset);

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

            assert_eq!(outset, b.as_str());
        }

        #[test]
        fn length_limits() {
            let outset = "do";

            let mut f = Vec::new();
            let mut b = String::from(outset);

            let mut n = Node::empty();

            let mut document = add_one(&mut n, "ument", true);
            let mut documental = add_one(&mut document, "al", true);
            _ = add_one(&mut documental, "ist", true);
            _ = add_one(&mut document, "able", true);
            _ = add_one(&mut document, "s", true);

            let mut extender = Extender {
                b: &mut b,
                f: &mut f,
                n: 5,
                nl: "document".len() + 1,
                xl: "documentalist".len() - 1,
            };

            let res = extender.e(&mut n, 'c');
            assert_eq!(false, res);
            let mut proof = vec![rev("documental"), rev("documentable"), rev("documents")];
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
        fn load_bearing_a() {
            let mut f = Vec::new();
            let mut b = String::from("ser");

            let (n, p) = load_setup();

            let mut extender = basic_ext(&mut b, &mut f, usize::MAX);
            _ = extender.e(&n, 'o');

            assert_eq!(p.len(), f.len());
            for f in f {
                assert_eq!(true, p.contains(&f), "{f}");
            }
        }

        #[test]
        fn load_bearing_b() {
            let mut f = Vec::new();
            let mut b = String::from("ser");

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
        use crate::{CharBuf, push_match};

        #[test]
        fn limit_hit_a() {
            let proof = "poetship";
            let cs = proof.chars().rev().collect::<CharBuf>();
            let mut f = Vec::new();

            let lim = push_match(&cs, &mut f, 2);
            assert_eq!(false, lim);
            assert_eq!(1, f.len());
            assert_eq!(proof, f[0]);
        }

        #[test]
        fn limit_hit_b() {
            let proof = "poet-cruiser";
            let cs = proof.chars().rev().collect::<CharBuf>();
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
                assert_eq!(2, mc.ext_ml);
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
            assert_eq!(mc_defaults::EXT_ML, mc.ext_ml);
            assert_eq!(mc_defaults::MAX_ML, mc.max_ml);
            assert_eq!(mc_defaults::SUB_E, mc.sub_e);
        }

        mod val {
            use crate::{MatchConduct, ReqErr};

            #[test]
            fn zero_n() {
                let mut mc = MatchConduct::test();
                mc.max_n = 0;

                let err = MatchConduct::val(&mc);
                assert_eq!(Some(ReqErr::ZeroMaxMatches), err);
            }

            #[test]
            fn zero_suffix_requirement() {
                let mut mc = MatchConduct::test();
                mc.min_sl = 0;

                let err = MatchConduct::val(&mc);
                assert_eq!(Some(ReqErr::ZeroMinSufLen), err);
            }

            #[test]
            fn suffix_min_greater_max() {
                let mut mc = MatchConduct::test();
                mc.min_sl = 1;
                mc.max_sl = 0;

                let err = MatchConduct::val(&mc);
                assert_eq!(Some(ReqErr::SufLenMaxLessThanMin), err);
            }

            #[test]
            fn suffix_min_equal_max() {
                let mut mc = MatchConduct::test();
                mc.min_sl = 1;
                mc.max_sl = 1;

                let res = MatchConduct::val(&mc);
                assert_eq!(None, res);
            }

            #[test]
            fn length_min_greater_max_a() {
                let mut mc = MatchConduct::test();
                mc.ext_ml = 1;
                mc.max_ml = 1;

                let err = MatchConduct::val(&mc);
                assert_eq!(Some(ReqErr::MatchLenMaxLessThanMin), err);
            }

            #[test]
            fn length_min_greater_max_b() {
                let mut mc = MatchConduct::test();
                mc.min_sl = 2;
                mc.max_ml = 1;

                let err = MatchConduct::val(&mc);
                assert_eq!(Some(ReqErr::MatchLenMaxLessThanMin), err);
            }

            #[test]
            fn length_min_equal_max_a() {
                let mut mc = MatchConduct::test();
                mc.ext_ml = 1;
                mc.max_ml = 2;

                let res = MatchConduct::val(&mc);
                assert_eq!(None, res);
            }

            #[test]
            fn length_min_equal_max_b() {
                let mut mc = MatchConduct::test();
                mc.min_sl = 2;
                mc.max_ml = 2;

                let res = MatchConduct::val(&mc);
                assert_eq!(None, res);
            }

            #[test]
            fn length_max_less_than_suffix_max() {
                // logically not problem
                // even connotes with concept of unbound
                // suffix, usize::MAX, still can be understood
                // as miscofiguration, kept loose
                let mut mc = MatchConduct::test();
                mc.max_ml = 1;
                mc.max_sl = 2;

                let none = MatchConduct::val(&mc);
                assert_eq!(None, none);
            }

            #[test]
            fn suffix_max_less_than_length_max() {
                let mut mc = MatchConduct::test();
                mc.max_ml = 2;
                mc.max_sl = 1;

                let res = MatchConduct::val(&mc);
                assert_eq!(None, res);
            }
        }

        #[test]
        fn max_o_sl() {
            let three_3 = 333;
            let three_7 = 777;

            let mut mc = MatchConduct::test();
            for duo in [(three_3, three_7), (three_7, three_3)] {
                mc.max_sl = duo.0;
                mc.max_ml = duo.1;

                assert_eq!(three_3, mc.max_o_sl());
            }
        }

        #[test]
        fn min_ml() {
            let mut mc = MatchConduct::test();
            mc.min_sl = 556;
            mc.ext_ml = 444;

            assert_eq!(1000, mc.min_ml());
        }
    }

    mod match_conduct_shaper {
        use crate::{MatchConduct, MatchConductShaper, mc_defaults};

        #[test]
        fn basic_test() {
            let mut shaper = MatchConductShaper::init();
            let test = shaper
                .max_n(11)
                .min_sl(33)
                .max_sl(55)
                .ext_ml(22)
                .max_ml(77)
                .sub_e(true)
                .form();

            let proof = MatchConduct {
                max_n: 11,
                min_sl: 33,
                max_sl: 55,
                ext_ml: 22,
                max_ml: 77,
                sub_e: true,
            };

            assert_ne!(mc_defaults::SUB_E, proof.sub_e);

            assert_eq!(Ok(proof.clone()), test);

            let test = shaper.transform();
            assert_eq!(Ok(proof), test);
        }

        #[test]
        fn default() {
            let shaper = MatchConductShaper::init();

            assert_eq!(MatchConduct::default(), shaper.0);
        }

        #[test]
        fn validation_form() {
            let mut shaper = MatchConductShaper::init();
            let err = shaper.max_n(0).form();

            assert_eq!(true, err.is_err());
        }

        #[test]
        fn validation_transform() {
            let mut shaper = MatchConductShaper::init();
            _ = shaper.max_n(0);
            let err = shaper.transform();
            assert_eq!(true, err.is_err());

            let (_, test) = err.unwrap_err();
            let mut proof = MatchConductShaper::init();
            _ = proof.max_n(0);
            assert_eq!(proof, test);
        }
    }

    pub mod poetrie {
        use crate::{Node, Poetrie};

        #[test]
        fn nw() {
            let poetrie = Poetrie::nw();

            assert_eq!(Node::empty(), poetrie.root);
            assert_eq!(0, poetrie.cnt);

            test_vec(&poetrie.btr);
            test_vec(&poetrie.bra);

            let buf = poetrie.buf.aq_ref();
            assert_eq!(0, buf.len());
            assert_eq!(0, buf.capacity());

            fn test_vec<T>(buf: &Vec<T>) {
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
                    let node = links.get(&c);

                    assert_eq!(true, node.is_some());
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
                let mc = MatchConduct::test();
                let find = poetrie.sx(&key, &mc);

                assert_eq!(Ok(vec![proof]), find);
            }

            #[test]
            fn err() {
                let poetrie = Poetrie::nw();

                let key = Entry("semiliteral");
                let mc = MatchConduct::test();
                let res = poetrie.sx(&key, &mc);
                assert_eq!(Err(FindErr::EmptyTree), res);
            }

            #[test]
            fn stores_clearing() {
                let mut poetrie = Poetrie::nw();

                let e = Entry("semiliteral");
                let ke = Entry("quadriliteral");
                _ = poetrie.it(&e);
                _ = poetrie.it(&ke);

                assert_eq!(0, poetrie.buf.capacity());
                assert_eq!(0, poetrie.bra.capacity());

                let mc = MatchConduct::test();
                _ = poetrie.sx(&ke, &mc);
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

            let bra = poetrie.bra.promote();
            let buf = poetrie.buf.promote();

            bra.push((ptr::null(), 0, ptr::null()));
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

                let mut grade = 0;
                poetrie.re_actual(&mut grade);
                assert_eq!(false, poetrie.ey(entry));
                assert_eq!(18, grade);
            }

            #[test]
            fn one_letter_b() {
                let entry1 = &Entry("a");
                let entry2 = &Entry("b");

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(entry1);
                _ = poetrie.it(entry2);
                _ = poetrie.track(entry1, true);

                let mut grade = 0;
                poetrie.re_actual(&mut grade);
                assert_eq!(false, poetrie.ey(entry1));
                assert_eq!(true, poetrie.ey(entry2));
                assert_eq!(6, grade);
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

                let mut grade = 0;
                poetrie.re_actual(&mut grade);
                assert_eq!(false, poetrie.ey(entry1));
                assert_eq!(true, poetrie.ey(entry2));
                assert_eq!(1, grade);
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

                let mut grade = 0;
                _ = poetrie.track(inner, true);

                poetrie.re_actual(&mut grade);
                assert_eq!(1, grade);

                assert_eq!(false, poetrie.ey(inner));
                assert_eq!(true, poetrie.ey(outer));
            }

            #[test]
            fn links_removal() {
                let entry = RevEntry::new("Keyword");
                let entry = &entry.entry();
                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(entry);

                let mut grade = 0;
                _ = poetrie.track(entry, true);
                poetrie.re_actual(&mut grade);
                assert_eq!(18, grade);

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

                let mut grade = 0;
                _ = poetrie.track(keyword, true);
                poetrie.re_actual(&mut grade);
                assert_eq!(6, grade);

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

                let mut grade = 0;
                _ = poetrie.track(under, true);
                poetrie.re_actual(&mut grade);
                assert_eq!(10, grade);

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

        pub mod find {
            use std::cmp::min;
            use std::collections::HashSet;

            use crate::{
                Entry, FindErr, MatchConduct, Poetrie, mc_defaults::MAX_ML,
                tests_of_units::rev_entry::RevEntry,
            };

            pub mod grade {
                /// key exhausted
                pub const KEY_EXH: usize = 2;
                /// no path available on node
                pub const NO_PATH_N: usize = 4;
                /// no path available on link
                pub const NO_PATH_L: usize = 8;
                /// guaranteed zero matches
                pub const G_ZERO_M: usize = 16;
                /// only sub-entries available
                pub const SUB_E_ONLY: usize = 32;
                /// matches requirement satisfied on sub-entry
                pub const SAT_ON_SE: usize = 64;
                /// matches requirement satisfied on extension
                pub const SAT_ON_EXT: usize = 128;
                /// matches requirement satisfied on branching
                pub const SAT_ON_BRA: usize = 256;
                /// final execution reached
                pub const FIN: usize = 512;
                /// buffer is already at maximum length on branch node
                pub const BUF_MAX_ALR: usize = 1024;
                /// min suffix requirement not reached
                pub const MIN_SL_NOT_REA: usize = 2048;
            }

            #[test]
            fn basic_test() {
                let p = ["halieutics", "codecs"].map(|x| String::from(x));

                let mut poetrie = Poetrie::nw();
                for p in p.iter() {
                    let entry = Entry(p.as_str());
                    _ = poetrie.it(&entry);
                }

                let k = &Entry("lyrics");
                let mut mc = MatchConduct::test();
                mc.max_n = usize::MAX;

                let f = poetrie.find(k, &mc, &mut 0).ok().unwrap();

                assert_eq!(p.len(), f.len());
                for p in p {
                    assert_eq!(true, p == f[0] || p == f[1]);
                }
            }

            #[test]
            fn exactly_last_match_a_1() {
                let e = &Entry("s");
                let k = &Entry("lyrics");

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e);

                let mut mc = MatchConduct::test();
                mc.sub_e = true;
                mc.max_n = 2;

                for duo in [(1, 40), (MAX_ML, 40)] {
                    mc.max_ml = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);

                    poetrie.clr_f_buffs();

                    assert_eq!(Ok(vec![String::from("s")]), f, "{duo:?}");
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn exactly_last_match_a_2() {
                let e = &Entry("s");
                let k = &Entry("lyrics");

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e);
                _ = poetrie.it(k);

                let mut mc = MatchConduct::test();
                mc.sub_e = true;
                mc.max_n = 2;

                for duo in [(1, 34), (MAX_ML, 34)] {
                    mc.max_ml = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);

                    poetrie.clr_f_buffs();

                    assert_eq!(Ok(vec![String::from("s")]), f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn exactly_last_match_b_1() {
                let p = "lyrics";
                let k = &Entry("s");

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&Entry(p));

                let mut mc = MatchConduct::test();

                for duo in [(1, 130), (usize::MAX, 514)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);

                    poetrie.clr_f_buffs();

                    let proof = vec![String::from(p)];
                    assert_eq!(Ok(proof), f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn exactly_last_match_b_2() {
                let p = "lyrics";

                let k = &Entry("s");

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&Entry(p));
                _ = poetrie.it(k);

                let mut mc = MatchConduct::test();
                for duo in [(1, 130), (usize::MAX, 514)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;

                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    let proof = vec![String::from(p)];
                    assert_eq!(Ok(proof), f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn exactly_last_match_c() {
                let k = &Entry("s");

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(k);

                let mut mc = MatchConduct::test();
                for max_ml in [1, MAX_ML] {
                    mc.max_ml = max_ml;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);

                    poetrie.clr_f_buffs();

                    assert_eq!(Err(FindErr::OnlyKeyMatches), f);
                    assert_eq!(18, grade);
                }
            }

            #[test]
            fn no_data() {
                let k = &Entry("lyrics");
                let mc = MatchConduct::test();

                let poetrie = Poetrie::nw();

                let mut grade = 0;
                let f = poetrie.find(k, &mc, &mut grade);

                assert_eq!(Err(FindErr::EmptyTree), f);
                assert_eq!(0, grade);
            }

            #[test]
            fn no_suffix_match() {
                let e = &Entry("epicalyx");
                let k = &Entry("lyrics");
                let mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e);

                let mut grade = 0;
                let f = poetrie.find(k, &mc, &mut grade);

                assert_eq!(Err(FindErr::NoJointSuffix), f);
                assert_eq!(0, grade);
            }

            #[test]
            fn key_matches_itself_only_a_1() {
                let itself = &Entry("lyrics");
                let mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(itself);

                let mut grade = 0;
                let f = poetrie.find(itself, &mc, &mut grade);

                assert_eq!(Err(FindErr::OnlyKeyMatches), f);
                assert_eq!(18, grade);
            }

            #[test]
            fn key_matches_itself_only_a_2() {
                let itself = &Entry("lyrics");
                let mut mc = MatchConduct::test();
                mc.max_ml = itself.0.len() - 1;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(itself);

                let mut grade = 0;
                let f = poetrie.find(itself, &mc, &mut grade);

                assert_eq!(Err(FindErr::OnlyKeyMatches), f);
                assert_eq!(18, grade);
            }

            #[test]
            fn key_matches_itself_only_a_3() {
                let itself = &Entry("lyrics");
                let mut mc = MatchConduct::test();
                mc.max_sl = itself.0.len() - 1;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(itself);

                let mut grade = 0;
                let f = poetrie.find(itself, &mc, &mut grade);

                assert_eq!(Err(FindErr::OnlyKeyMatches), f);
                assert_eq!(18, grade);
            }

            #[test]
            fn key_matches_itself_only_b() {
                let p = String::from("lyRics");
                let e = &Entry(p.as_str());
                let k = &Entry("lyrics");
                let mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e);
                _ = poetrie.it(k);

                let mut grade = 0;
                let f = poetrie.find(k, &mc, &mut grade);

                assert_eq!(Ok(vec![p]), f);
                assert_eq!(258, grade);
            }

            #[test]
            fn subentry_disjunct_detection_a_1() {
                let se = RevEntry::new("document");
                let k = RevEntry::new("documentalist");

                let mut mc = MatchConduct::test();
                mc.sub_e = false;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());

                let mut grade = 0;
                let f = poetrie.find(&k.entry(), &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(24, grade);
            }

            #[test]
            fn subentry_disjunct_detection_a_2() {
                let se = RevEntry::new("document");
                let k = RevEntry::new("documentalist");
                let k = &k.entry();

                let mut mc = MatchConduct::test();
                mc.sub_e = false;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());
                _ = poetrie.it(k);

                let mut grade = 0;
                let f = poetrie.find(k, &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(18, grade);
            }

            #[test]
            fn subentry_disjunct_detection_b_1() {
                let se = RevEntry::new("document");
                let k = RevEntry::new("documentalist");

                let mut mc = MatchConduct::test();
                mc.sub_e = true;
                mc.min_sl = se.0.len() + 1;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());

                let mut grade = 0;
                let f = poetrie.find(&k.entry(), &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(2056, grade);
            }

            #[test]
            fn subentry_disjunct_detection_b_2() {
                let se = RevEntry::new("document");
                let k = RevEntry::new("documentalist");
                let k = &k.entry();

                let mut mc = MatchConduct::test();
                mc.sub_e = true;
                mc.min_sl = se.0.len() + 1;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());
                _ = poetrie.it(k);

                let mut grade = 0;
                let f = poetrie.find(k, &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(18, grade);
            }

            #[test]
            fn subentry_disjunct_detection_b_3() {
                let se = RevEntry::new("document");
                let k = RevEntry::new("documentalist");

                let mut mc = MatchConduct::test();
                mc.sub_e = true;
                mc.min_sl = se.0.len();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());

                let p = Ok(vec![se.0]);
                for duo in [(1, 64), (usize::MAX, 40)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(&k.entry(), &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn subentry_disjunct_detection_b_4() {
                let se = RevEntry::new("document");
                let k = RevEntry::new("documentalist");
                let k = &k.entry();

                let mut mc = MatchConduct::test();
                mc.sub_e = true;
                mc.min_sl = se.0.len();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());
                _ = poetrie.it(k);

                let p = Ok(vec![se.0]);
                for duo in [(1, 64), (usize::MAX, 34)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn subentry_disjunct_detection_c_1() {
                let se = RevEntry::new("document");
                let k = RevEntry::new("documentalist");

                let mut mc = MatchConduct::test();
                mc.sub_e = true;
                mc.min_sl = se.0.len();
                mc.ext_ml = 1;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());

                let mut grade = 0;
                let f = poetrie.find(&k.entry(), &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(24, grade);
            }

            #[test]
            fn subentry_disjunct_detection_c_2() {
                let se = RevEntry::new("document");
                let k = RevEntry::new("documentalist");
                let k = &k.entry();

                let mut mc = MatchConduct::test();
                mc.sub_e = true;
                mc.min_sl = se.0.len();
                mc.ext_ml = 1;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());
                _ = poetrie.it(k);

                let mut grade = 0;
                let f = poetrie.find(k, &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(18, grade);
            }

            #[test]
            fn subentry_disjunct_detection_c_3() {
                let se = RevEntry::new("document");
                let k = RevEntry::new("documentalist");

                let mut mc = MatchConduct::test();
                mc.sub_e = true;
                mc.min_sl = se.0.len();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());

                let p = Ok(vec![se.0]);
                for duo in [(1, 64), (usize::MAX, 40)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(&k.entry(), &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn subentry_disjunct_detection_c_4() {
                let se = RevEntry::new("document");
                let k = RevEntry::new("documentalist");
                let k = &k.entry();

                let mut mc = MatchConduct::test();
                mc.sub_e = true;
                mc.min_sl = se.0.len();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());
                _ = poetrie.it(k);

                let p = Ok(vec![se.0]);
                for duo in [(1, 64), (usize::MAX, 34)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn subentry_disjunct_detection_d_1() {
                let se = RevEntry::new("document");
                let k = RevEntry::new("documentalist");

                let mut mc = MatchConduct::test();
                mc.sub_e = true;
                mc.max_sl = se.0.len() - 1;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());

                let mut grade = 0;
                let f = poetrie.find(&k.entry(), &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(24, grade);
            }

            #[test]
            fn subentry_disjunct_detection_d_2() {
                let se = RevEntry::new("document");
                let k = RevEntry::new("documentalist");
                let k = &k.entry();

                let mut mc = MatchConduct::test();
                mc.sub_e = true;
                mc.max_sl = se.0.len() - 1;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());
                _ = poetrie.it(k);

                let mut grade = 0;
                let f = poetrie.find(k, &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(18, grade);
            }

            #[test]
            fn subentry_disjunct_detection_d_3() {
                let se = RevEntry::new("document");
                let k = RevEntry::new("documentalist");

                let mut mc = MatchConduct::test();
                mc.sub_e = true;
                mc.max_sl = se.0.len();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());

                let p = Ok(vec![se.0]);
                for duo in [(1, 64), (usize::MAX, 40)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(&k.entry(), &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn subentry_disjunct_detection_d_4() {
                let se = RevEntry::new("document");
                let k = RevEntry::new("documentalist");
                let k = &k.entry();

                let mut mc = MatchConduct::test();
                mc.sub_e = true;
                mc.max_sl = se.0.len();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());
                _ = poetrie.it(k);

                let p = Ok(vec![se.0]);
                for duo in [(1, 64), (usize::MAX, 34)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn subentry_disjunct_detection_e_1() {
                let se = RevEntry::new("document");
                let k = RevEntry::new("documentalist");

                let mut mc = MatchConduct::test();
                mc.sub_e = true;
                mc.max_ml = se.0.len() - 1;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());

                let mut grade = 0;
                let f = poetrie.find(&k.entry(), &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(24, grade);
            }

            #[test]
            fn subentry_disjunct_detection_e_2() {
                let se = RevEntry::new("document");
                let k = RevEntry::new("documentalist");
                let k = &k.entry();

                let mut mc = MatchConduct::test();
                mc.sub_e = true;
                mc.max_ml = se.0.len() - 1;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());
                _ = poetrie.it(k);

                let mut grade = 0;
                let f = poetrie.find(k, &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(18, grade);
            }

            #[test]
            fn subentry_disjunct_detection_e_3() {
                let se = RevEntry::new("document");
                let k = RevEntry::new("documentalist");

                let mut mc = MatchConduct::test();
                mc.sub_e = true;
                mc.max_ml = se.0.len();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());

                let p = Ok(vec![se.0]);
                for duo in [(1, 64), (usize::MAX, 40)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(&k.entry(), &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn subentry_disjunct_detection_e_4() {
                let se = RevEntry::new("document");
                let k = RevEntry::new("documentalist");
                let k = &k.entry();

                let mut mc = MatchConduct::test();
                mc.sub_e = true;
                mc.max_ml = se.0.len();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());
                _ = poetrie.it(k);

                let p = Ok(vec![se.0]);
                for duo in [(1, 64), (usize::MAX, 34)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn saturation_on_sub_entry() {
                let e_a = RevEntry::new("document");
                let e_b = RevEntry::new("documental");
                let k = RevEntry::new("documentalist");

                let mut mc = MatchConduct::test();
                mc.sub_e = true;
                mc.max_n = 2;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e_a.entry());
                _ = poetrie.it(&e_b.entry());

                let mut grade = 0;
                let f = poetrie.find(&k.entry(), &mc, &mut grade);

                let p = Ok(vec![e_a.0, e_b.0]);
                assert_eq!(p, f);
                assert_eq!(64, grade);
            }

            #[test]
            fn branch_disjunct_detection_a_1() {
                let e = RevEntry::new("documenter");
                let k = RevEntry::new("documentalist");

                let mut mc = MatchConduct::test();
                mc.min_sl = e.0.len() - 1;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e.entry());

                let mut grade = 0;
                let f = poetrie.find(&k.entry(), &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(2052, grade);
            }

            #[test]
            fn branch_disjunct_detection_a_2() {
                let e = RevEntry::new("documenter");
                let k = RevEntry::new("documentalist");
                let k = &k.entry();

                let mut mc = MatchConduct::test();
                mc.min_sl = e.0.len() - 1;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e.entry());
                _ = poetrie.it(k);

                let mut grade = 0;
                let f = poetrie.find(k, &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(18, grade);
            }

            #[test]
            fn branch_disjunct_detection_a_3() {
                let e = RevEntry::new("documenter");
                let k = RevEntry::new("documentalist");

                let mut mc = MatchConduct::test();
                mc.min_sl = e.0.len() - 2;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e.entry());

                let p = Ok(vec![e.0]);
                for duo in [(1, 132), (usize::MAX, 516)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(&k.entry(), &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn branch_disjunct_detection_a_4() {
                let e = RevEntry::new("documenter");
                let k = RevEntry::new("documentalist");
                let k = &k.entry();

                let mut mc = MatchConduct::test();
                mc.min_sl = e.0.len() - 2;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e.entry());
                _ = poetrie.it(k);

                let p = Ok(vec![e.0]);
                for duo in [(1, 258), (usize::MAX, 514)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f, "{}", duo.1);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn branch_disjunct_detection_b_1() {
                let e = RevEntry::new("documenter");
                let k = RevEntry::new("documentalist");

                let mut mc = MatchConduct::test();
                mc.max_sl = e.0.len() - 3;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e.entry());

                let mut grade = 0;
                let f = poetrie.find(&k.entry(), &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(20, grade);
            }

            #[test]
            fn branch_disjunct_detection_b_2() {
                let e = RevEntry::new("documenter");
                let k = RevEntry::new("documentalist");
                let k = &k.entry();

                let mut mc = MatchConduct::test();
                mc.max_sl = e.0.len() - 3;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e.entry());
                _ = poetrie.it(k);

                let mut grade = 0;
                let f = poetrie.find(k, &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(18, grade);
            }

            #[test]
            fn branch_disjunct_detection_b_3() {
                let e = RevEntry::new("documenter");
                let k = RevEntry::new("documentalist");

                let mut mc = MatchConduct::test();
                mc.max_sl = e.0.len() - 2;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e.entry());

                let p = Ok(vec![e.0]);
                for duo in [(1, 132), (usize::MAX, 516)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(&k.entry(), &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn branch_disjunct_detection_b_4() {
                let e = RevEntry::new("documenter");
                let k = RevEntry::new("documentalist");
                let k = &k.entry();

                let mut mc = MatchConduct::test();
                mc.max_sl = e.0.len() - 2;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e.entry());
                _ = poetrie.it(k);

                let p = Ok(vec![e.0]);
                for duo in [(1, 258), (usize::MAX, 514)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f, "{:?}, grade: {grade}", duo);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn branch_disjunct_detection_c_1() {
                let e = RevEntry::new("documenter");
                let k = RevEntry::new("documentalist");

                let mut mc = MatchConduct::test();
                mc.max_ml = e.0.len() - 3;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e.entry());

                let mut grade = 0;
                let f = poetrie.find(&k.entry(), &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(20, grade);
            }

            #[test]
            fn branch_disjunct_detection_c_2() {
                let e = RevEntry::new("documenter");
                let k = RevEntry::new("documentalist");
                let k = &k.entry();

                let mut mc = MatchConduct::test();
                mc.max_ml = e.0.len() - 3;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e.entry());
                _ = poetrie.it(k);

                let mut grade = 0;
                let f = poetrie.find(k, &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(18, grade);
            }

            #[test]
            fn branch_disjunct_detection_c_3() {
                let e = RevEntry::new("documenter");
                let k = RevEntry::new("documentalist");

                let mut mc = MatchConduct::test();
                let e_len = e.0.len();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e.entry());

                let p = Ok(vec![e.0]);
                for quadruplet in [
                    (usize::MAX, 20, e_len - 2, Err(FindErr::DisjunctConduct)),
                    (usize::MAX, 516, e_len - 1, Err(FindErr::DisjunctConduct)),
                    (1, 132, e_len, p.clone()),
                    (usize::MAX, 516, e_len, p),
                ] {
                    mc.max_n = quadruplet.0;
                    mc.max_ml = quadruplet.2;

                    let mut grade = 0;
                    let f = poetrie.find(&k.entry(), &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(quadruplet.3, f);
                    assert_eq!(quadruplet.1, grade);
                }
            }

            #[test]
            fn branch_disjunct_detection_c_4() {
                let e = RevEntry::new("documenter");
                let k = RevEntry::new("documentalist");
                let k = &k.entry();

                let mut mc = MatchConduct::test();
                let e_len = e.0.len();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e.entry());
                _ = poetrie.it(k);

                let p = Ok(vec![e.0]);
                for quadruplet in [
                    (usize::MAX, 1538, e_len - 2, Err(FindErr::DisjunctConduct)),
                    (usize::MAX, 514, e_len - 1, Err(FindErr::DisjunctConduct)),
                    (1, 258, e_len, p.clone()),
                    (usize::MAX, 514, e_len, p),
                ] {
                    mc.max_n = quadruplet.0;
                    mc.max_ml = quadruplet.2;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(quadruplet.3, f);
                    assert_eq!(quadruplet.1, grade, "{quadruplet:?}");
                }
            }

            #[test]
            fn minimal_suffix_length_miss_a_1() {
                let e_a = RevEntry::new("document");
                let e_b = RevEntry::new("documenter");
                let k = RevEntry::new("documentalist");

                let mut mc = MatchConduct::test();
                mc.min_sl = e_b.0.len() + 1;
                mc.sub_e = true;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e_a.entry());
                _ = poetrie.it(&e_b.entry());

                let mut grade = 0;
                let f = poetrie.find(&k.entry(), &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(2052, grade);
            }

            #[test]
            fn minimal_suffix_length_miss_a_2() {
                let e_a = RevEntry::new("document");
                let e_b = RevEntry::new("documenter");
                let k = RevEntry::new("documentalist");
                let k = &k.entry();

                let mut mc = MatchConduct::test();
                mc.min_sl = k.0.len() + 1;
                mc.sub_e = true;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e_a.entry());
                _ = poetrie.it(&e_b.entry());
                _ = poetrie.it(k);

                let mut grade = 0;
                let f = poetrie.find(k, &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(2050, grade);
            }

            #[test]
            fn minimal_suffix_length_miss_a_3() {
                let e_a = RevEntry::new("document");
                let e_b = RevEntry::new("documenter");
                let k = RevEntry::new("documentalist");

                let mut mc = MatchConduct::test();
                mc.min_sl = e_a.0.len();
                mc.sub_e = true;
                mc.max_n = usize::MAX;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e_a.entry());
                _ = poetrie.it(&e_b.entry());

                let mut grade = 0;
                let f = poetrie.find(&k.entry(), &mc, &mut grade);

                let p = Ok(vec![e_a.0, e_b.0]);
                assert_eq!(p, f);
                assert_eq!(516, grade);
            }

            #[test]
            fn minimal_suffix_length_miss_a_4() {
                let e_a = RevEntry::new("document");
                let e_b = RevEntry::new("documenter");
                let k = RevEntry::new("documentalist");
                let k = &k.entry();

                let mut mc = MatchConduct::test();
                mc.min_sl = e_a.0.len();
                mc.sub_e = true;
                mc.max_n = usize::MAX;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e_a.entry());
                _ = poetrie.it(&e_b.entry());
                _ = poetrie.it(k);

                let mut grade = 0;
                let f = poetrie.find(k, &mc, &mut grade);

                let p = Ok(vec![e_a.0, e_b.0]);
                assert_eq!(p, f);
                assert_eq!(514, grade);
            }

            #[test]
            fn cannot_extend_a_1() {
                let e = RevEntry::new("documentalist");
                let k = RevEntry::new("document");

                let mut mc = MatchConduct::test();
                mc.max_sl = k.0.len() - 1;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e.entry());

                let mut grade = 0;
                let f = poetrie.find(&k.entry(), &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(18, grade);
            }

            #[test]
            fn cannot_extend_a_2() {
                let e = RevEntry::new("documentalist");
                let k = RevEntry::new("document");

                let mut mc = MatchConduct::test();
                mc.max_sl = k.0.len();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e.entry());

                let mut grade = 0;
                let f = poetrie.find(&k.entry(), &mc, &mut grade);

                assert_eq!(Ok(vec![e.0]), f);
                assert_eq!(130, grade);
            }

            #[test]
            fn cannot_extend_b_1() {
                let e = RevEntry::new("documentalist");
                let k = RevEntry::new("document");

                let mut mc = MatchConduct::test();
                mc.max_ml = k.0.len();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e.entry());

                let mut grade = 0;
                let f = poetrie.find(&k.entry(), &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(18, grade);
            }

            #[test]
            fn cannot_extend_b_2() {
                let e = RevEntry::new("documentalist");
                let k = RevEntry::new("document");
                let k = &k.entry();

                let mut mc = MatchConduct::test();
                mc.max_n = usize::MAX;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e.entry());

                let e = e.0;
                for duo in [
                    (Err(FindErr::DisjunctConduct), k.0.len() + 1),
                    (Ok(vec![e.clone()]), e.len()),
                ] {
                    mc.max_ml = duo.1;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(duo.0, f);
                    assert_eq!(514, grade);
                }
            }

            #[test]
            fn cannot_extend_c_1() {
                let k = RevEntry::new("document");
                let k = &k.entry();

                let mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(k);

                let mut grade = 0;
                let f = poetrie.find(k, &mc, &mut grade);

                assert_eq!(Err(FindErr::OnlyKeyMatches), f);
                assert_eq!(18, grade);
            }

            #[test]
            fn cannot_extend_c_2() {
                let e = RevEntry::new("document");
                let k = RevEntry::new("documentalist");
                let k = &k.entry();

                let mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e.entry());
                _ = poetrie.it(k);

                let mut grade = 0;
                let f = poetrie.find(k, &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(18, grade);
            }

            #[test]
            fn cannot_extend_d_1() {
                let e = RevEntry::new("document");
                let k = RevEntry::new("documentalist");

                let mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e.entry());

                let mut grade = 0;
                let f = poetrie.find(&k.entry(), &mc, &mut grade);

                assert_eq!(Err(FindErr::DisjunctConduct), f);
                assert_eq!(24, grade);
            }

            #[test]
            fn cannot_extend_d_2() {
                let e = RevEntry::new("document");
                let k = RevEntry::new("documentalist");

                let mut mc = MatchConduct::test();
                mc.sub_e = true;
                mc.max_n = usize::MAX;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e.entry());

                let mut grade = 0;
                let f = poetrie.find(&k.entry(), &mc, &mut grade);

                assert_eq!(Ok(vec![e.0]), f);
                assert_eq!(40, grade);
            }

            #[test]
            fn must_not_recourse_to_subentry_a() {
                let entries = ["document", "documenter", "documental", "docudrama"]
                    .map(rev_entry::rev)
                    .to_vec();

                let key = RevEntry::new("documented");
                let key = &key.entry();

                let mut poetrie = Poetrie::nw();
                for e in entries.iter() {
                    _ = poetrie.it(&Entry(e.as_str()));
                }

                let mut mc = MatchConduct::default();
                mc.max_n = usize::MAX;

                let mut proof = entries.clone();
                proof.remove(0);
                let proof = Ok(proof);

                let mut grade = 0;
                let mut f = poetrie.find(key, &mc, &mut grade);
                assert_eq!(proof, f);
                assert_eq!(516, grade);

                poetrie.clr_f_buffs();

                let proof = Ok(entries);
                mc.sub_e = true;

                grade = 0;
                f = poetrie.find(key, &mc, &mut grade);
                assert_eq!(proof, f);
                assert_eq!(516, grade);
            }

            #[test]
            fn must_not_recourse_to_subentry_b() {
                let entries = ["document", "documenter", "docudrama"]
                    .map(rev_entry::rev)
                    .to_vec();

                let key = RevEntry::new("documented");
                let key = &key.entry();

                let mut poetrie = Poetrie::nw();
                for e in entries.iter() {
                    _ = poetrie.it(&Entry(e.as_str()));
                }

                _ = poetrie.it(key);

                let mut mc = MatchConduct::default();
                mc.max_n = usize::MAX;

                let mut proof = entries.clone();
                proof.remove(0);
                let proof = Ok(proof);

                let mut grade = 0;
                let mut f = poetrie.find(key, &mc, &mut grade);
                assert_eq!(proof, f);
                assert_eq!(514, grade);

                poetrie.clr_f_buffs();

                let proof = Ok(entries);
                mc.sub_e = true;

                grade = 0;
                f = poetrie.find(key, &mc, &mut grade);
                assert_eq!(proof, f);
                assert_eq!(514, grade);
            }

            #[test]
            fn extension_a_1() {
                let e_a = RevEntry::new("documenting");
                let e_b = RevEntry::new("documenter");
                let e_c = RevEntry::new("documental");
                let e_d = RevEntry::new("documentalist");
                let e_e = RevEntry::new("documentational");
                let k = RevEntry::new("document");

                let mut poetrie = Poetrie::nw();

                _ = poetrie.it(&e_a.entry());
                _ = poetrie.it(&e_b.entry());
                _ = poetrie.it(&e_c.entry());
                _ = poetrie.it(&e_d.entry());
                _ = poetrie.it(&e_e.entry());

                let mut mc = MatchConduct::test();
                mc.ext_ml = e_b.0.len();
                mc.max_ml = e_e.0.len() - 1;

                let mut p = vec![e_a.0, e_d.0];
                p.sort();

                for duo in [(2, 130), (usize::MAX, 514)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(&k.entry(), &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    let mut f = f.unwrap();
                    f.sort();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn extension_a_2() {
                let e_a = RevEntry::new("documenting");
                let e_b = RevEntry::new("documenter");
                let e_c = RevEntry::new("documental");
                let e_d = RevEntry::new("documentalist");
                let e_e = RevEntry::new("documentational");
                let k = RevEntry::new("document");
                let k = &k.entry();

                let mut poetrie = Poetrie::nw();

                _ = poetrie.it(&e_a.entry());
                _ = poetrie.it(&e_b.entry());
                _ = poetrie.it(&e_c.entry());
                _ = poetrie.it(&e_d.entry());
                _ = poetrie.it(&e_e.entry());
                _ = poetrie.it(k);

                let mut mc = MatchConduct::test();
                mc.ext_ml = e_b.0.len();
                mc.max_ml = e_e.0.len() - 1;

                let mut p = vec![e_a.0, e_d.0];
                p.sort();

                for duo in [(2, 130), (usize::MAX, 514)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    let mut f = f.unwrap();
                    f.sort();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn extension_b_1() {
                let e_a = RevEntry::new("documenting");
                let e_b = RevEntry::new("documenter");
                let e_c = RevEntry::new("documental");
                let e_d = RevEntry::new("documentalist");
                let e_e = RevEntry::new("documentational");
                let k = RevEntry::new("document");

                let mut mc = MatchConduct::test();
                mc.ext_ml = e_b.0.len() - 1;
                mc.max_ml = e_e.0.len();

                let mut poetrie = Poetrie::nw();

                let entries = [e_a, e_b, e_c, e_d, e_e];
                for e in entries.iter() {
                    _ = poetrie.it(&e.entry());
                }

                let p = HashSet::<String>::from_iter(entries.iter().map(|x| x.0.clone()));
                let p_len = p.len();

                for duo in [(2, 130), (5, 130), (6, 514)] {
                    let max_n = duo.0;
                    mc.max_n = max_n;

                    let mut grade = 0;
                    let f = poetrie.find(&k.entry(), &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    let f = f.unwrap();

                    let len = min(max_n, p_len);
                    assert_eq!(len, f.len());

                    for f in f {
                        assert_eq!(true, p.contains(&f));
                    }

                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn extension_b_2() {
                let e_a = RevEntry::new("documenting");
                let e_b = RevEntry::new("documenter");
                let e_c = RevEntry::new("documental");
                let e_d = RevEntry::new("documentalist");
                let e_e = RevEntry::new("documentational");
                let k = RevEntry::new("document");
                let k = &k.entry();

                let mut mc = MatchConduct::test();
                mc.ext_ml = e_b.0.len() - 1;
                mc.max_ml = e_e.0.len();

                let mut poetrie = Poetrie::nw();

                let entries = vec![e_a, e_b, e_c, e_d, e_e];
                for e in entries.iter() {
                    _ = poetrie.it(&e.entry());
                }

                _ = poetrie.it(k);

                let p = HashSet::<String>::from_iter(entries.iter().map(|x| x.0.clone()));
                let p_len = p.len();

                for duo in [(2, 130), (5, 130), (6, 514)] {
                    let max_n = duo.0;
                    mc.max_n = max_n;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    let f = f.unwrap();

                    let len = min(max_n, p_len);
                    assert_eq!(len, f.len());

                    for f in f {
                        assert_eq!(true, p.contains(&f));
                    }
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn branching_a_1() {
                let e_a = RevEntry::new("documenting");
                let e_b = RevEntry::new("documenter");
                let e_c = RevEntry::new("documental");
                let e_d = RevEntry::new("documentalistic");
                let e_e = RevEntry::new("docuer");
                let e_f = RevEntry::new("document");
                let e_g = RevEntry::new("documentation");
                let k = RevEntry::new("documentational");

                let mut poetrie = Poetrie::nw();

                _ = poetrie.it(&e_a.entry());
                _ = poetrie.it(&e_b.entry());
                _ = poetrie.it(&e_c.entry());
                _ = poetrie.it(&e_d.entry());
                _ = poetrie.it(&e_e.entry());
                _ = poetrie.it(&e_f.entry());
                _ = poetrie.it(&e_g.entry());

                let mut mc = MatchConduct::test();
                mc.ext_ml = e_e.0.len();
                mc.max_ml = e_d.0.len() - 1;

                let mut p = vec![e_a.0, e_b.0, e_c.0];
                p.sort();

                for duo in [(3, 264), (usize::MAX, 520)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(&k.entry(), &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    let mut f = f.unwrap();
                    f.sort();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn branching_a_2() {
                let e_a = RevEntry::new("documenting");
                let e_b = RevEntry::new("documenter");
                let e_c = RevEntry::new("documental");
                let e_d = RevEntry::new("documentalistic");
                let e_e = RevEntry::new("docuer");
                let e_f = RevEntry::new("document");
                let e_g = RevEntry::new("documentation");
                let k = RevEntry::new("documentational");
                let k = &k.entry();

                let mut poetrie = Poetrie::nw();

                _ = poetrie.it(&e_a.entry());
                _ = poetrie.it(&e_b.entry());
                _ = poetrie.it(&e_c.entry());
                _ = poetrie.it(&e_d.entry());
                _ = poetrie.it(&e_e.entry());
                _ = poetrie.it(&e_f.entry());
                _ = poetrie.it(&e_g.entry());
                _ = poetrie.it(k);

                let mut mc = MatchConduct::test();
                mc.ext_ml = e_e.0.len();
                mc.max_ml = e_d.0.len() - 1;

                let mut p = vec![e_a.0, e_b.0, e_c.0];
                p.sort();

                for duo in [(3, 258), (usize::MAX, 514)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    let mut f = f.unwrap();
                    f.sort();

                    assert_eq!(p, f, "{duo:?}, {grade}");
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn branching_b_1() {
                let e_a = RevEntry::new("documenting");
                let e_b = RevEntry::new("documenter");
                let e_c = RevEntry::new("documental");
                let e_d = RevEntry::new("documentalistic");
                let e_e = RevEntry::new("docuer");
                let e_f = RevEntry::new("document");
                let e_g = RevEntry::new("documentation");
                let k = RevEntry::new("documentational");

                let mut poetrie = Poetrie::nw();

                let mut mc = MatchConduct::test();
                mc.ext_ml = e_e.0.len() - 1;
                mc.max_ml = e_d.0.len();

                let proof = vec![e_a, e_b, e_c, e_d, e_e];
                for e in proof.iter() {
                    _ = poetrie.it(&e.entry());
                }

                _ = poetrie.it(&e_f.entry());
                _ = poetrie.it(&e_g.entry());

                let p = HashSet::<String>::from_iter(proof.iter().map(|x| x.0.clone()));
                let p_len = p.len();

                for duo in [(3, 264), (5, 264), (usize::MAX, 520)] {
                    let max_n = duo.0;
                    mc.max_n = max_n;

                    let mut grade = 0;
                    let f = poetrie.find(&k.entry(), &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    let f = f.unwrap();

                    let len = min(max_n, p_len);
                    assert_eq!(len, f.len(), "{duo:?}, {grade}, {f:?}");

                    for f in f {
                        assert_eq!(true, p.contains(&f), "{duo:?}, {grade}, {f}");
                    }

                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn branching_b_2() {
                let e_a = RevEntry::new("documenting");
                let e_b = RevEntry::new("documenter");
                let e_c = RevEntry::new("documental");
                let e_d = RevEntry::new("documentalistic");
                let e_e = RevEntry::new("docuer");
                let e_f = RevEntry::new("document");
                let e_g = RevEntry::new("documentation");
                let k = RevEntry::new("documentational");
                let k = &k.entry();

                let mut poetrie = Poetrie::nw();

                let mut mc = MatchConduct::test();
                mc.ext_ml = e_e.0.len() - 1;
                mc.max_ml = e_d.0.len();

                let proof = vec![e_a, e_b, e_c, e_d, e_e];
                for e in proof.iter() {
                    _ = poetrie.it(&e.entry());
                }

                _ = poetrie.it(&e_f.entry());
                _ = poetrie.it(&e_g.entry());
                _ = poetrie.it(k);

                let p = HashSet::<String>::from_iter(proof.iter().map(|x| x.0.clone()));
                let p_len = p.len();

                for duo in [(3, 258), (5, 258), (usize::MAX, 514)] {
                    let max_n = duo.0;
                    mc.max_n = max_n;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    let f = f.unwrap();

                    let len = min(max_n, p_len);
                    assert_eq!(len, f.len(), "{duo:?}, {grade}, {f:?}");

                    for f in f {
                        assert_eq!(true, p.contains(&f), "{duo:?}, {grade}, {f}");
                    }

                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn branching_obeys_max_length_precondition() {
                let e_a = RevEntry::new("docudrama");
                let e_b = RevEntry::new("documentarize");
                let k = RevEntry::new("documentarist");
                let k = &k.entry();

                let mut mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e_a.entry());
                _ = poetrie.it(&e_b.entry());
                _ = poetrie.it(k);

                let eb_len = e_b.len();

                for duo in [(2, 1282, vec![e_a.0.clone()]), (0, 258, vec![e_b.0, e_a.0])] {
                    // subtrahend
                    let s = duo.0;

                    mc.max_ml = eb_len - s;
                    mc.max_n = 2 - s / 2;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(Ok(duo.2), f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn key_with_subentry_is_suffix_to_entry_1() {
                let se = RevEntry::new("document");
                let e = RevEntry::new("documentalist");
                let k = RevEntry::new("documental");

                let mut mc = MatchConduct::test();
                mc.sub_e = true;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());
                _ = poetrie.it(&e.entry());

                let p = Ok(vec![se.0, e.0]);
                for duo in [(2, 130), (usize::MAX, 514)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(&k.entry(), &mc, &mut grade);

                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn key_with_subentry_is_suffix_to_entry_2() {
                let se = RevEntry::new("document");
                let e = RevEntry::new("documentalist");

                let k = RevEntry::new("documental");
                let k = &k.entry();

                let mut mc = MatchConduct::test();
                mc.sub_e = true;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se.entry());
                _ = poetrie.it(&e.entry());
                _ = poetrie.it(k);

                let p = Ok(vec![se.0, e.0]);
                for duo in [(2, 130), (usize::MAX, 514)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);

                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
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

                let mut mc = MatchConduct::test();
                mc.sub_e = true;

                let p = Ok(vec![se_a.0, se_b.0]);
                for duo in [(2, 64), (usize::MAX, 34)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let find = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, find);
                    assert_eq!(duo.1, grade);
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

                let mut mc = MatchConduct::test();
                mc.sub_e = true;

                let p = Ok(vec![se_a.0, se_b.0]);
                for duo in [(2, 64), (usize::MAX, 40)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let find = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, find);
                    assert_eq!(duo.1, grade);
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

                let mut mc = MatchConduct::test();
                mc.sub_e = true;

                let p = Ok(vec![p]);
                for duo in [(1, 64), (usize::MAX, 34)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn matches_subentries_b_2() {
                let p = String::from("m");
                let se = Entry(p.as_str());

                let k = &Entry("anagram");
                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se);

                let mut mc = MatchConduct::test();
                mc.sub_e = true;

                let p = Ok(vec![p]);
                for duo in [(1, 64), (usize::MAX, 40)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn matches_subentries_c_1() {
                let p = String::from("-ode");
                let se = Entry(p.as_str());

                let k = &Entry("X-ode");
                let mut mc = MatchConduct::test();
                mc.sub_e = true;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se);
                _ = poetrie.it(&k);

                let p = Ok(vec![p]);
                for duo in [(1, 64), (usize::MAX, 34)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn matches_subentries_c_2() {
                let p = String::from("-ode");
                let se = Entry(p.as_str());

                let k = &Entry("X-ode");
                let mut mc = MatchConduct::test();
                mc.sub_e = true;

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&se);

                let p = Ok(vec![p]);
                for duo in [(1, 64), (usize::MAX, 40)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn must_not_recourse_to_root_branching_a_1() {
                let p = String::from("hilum");
                let e_a = Entry(p.as_str());
                let e_b = Entry("claybank");

                let k = &Entry("haulm");
                let mut mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e_a);
                _ = poetrie.it(&e_b);
                _ = poetrie.it(k);

                let p = Ok(vec![p]);
                for duo in [(1, 258), (usize::MAX, 514)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn must_not_recourse_to_root_branching_a_2() {
                let p = String::from("hilum");
                let e_a = Entry(p.as_str());
                let e_b = Entry("claybank");

                let k = &Entry("haulm");
                let mut mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&e_a);
                _ = poetrie.it(&e_b);

                let p = Ok(vec![p]);
                for duo in [(1, 132), (usize::MAX, 516)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn must_not_recourse_to_root_branching_b() {
                let k = &Entry("lyrics");
                let e = &Entry("disarrangement");
                let mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(k);
                _ = poetrie.it(e);

                let mut grade = 0;
                let f = poetrie.find(k, &mc, &mut grade);

                assert_eq!(Err(FindErr::OnlyKeyMatches), f);
                assert_eq!(18, grade);
            }

            #[test]
            fn partially_shared_suffix_a_1() {
                let p = String::from("lyrics");
                let e = &Entry(p.as_str());

                let k = &Entry("athletics");
                let mut mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e);

                let p = Ok(vec![p]);
                for duo in [(1, 132), (usize::MAX, 516)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn partially_shared_suffix_a_2() {
                let p = String::from("lyrics");
                let e = &Entry(p.as_str());

                let k = &Entry("athletics");
                let mut mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e);
                _ = poetrie.it(k);

                let p = Ok(vec![p]);
                for duo in [(1, 258), (usize::MAX, 514)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn partially_shared_suffix_b_1() {
                let p = String::from("lyrics");
                let e = &Entry(p.as_str());

                let k = &Entry("carboniferous");
                let mut mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e);

                let p = Ok(vec![p]);
                for duo in [(1, 132), (usize::MAX, 516)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn partially_shared_suffix_b_2() {
                let p = String::from("lyrics");
                let e = &Entry(p.as_str());

                let k = &Entry("carboniferous");
                let mut mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e);
                _ = poetrie.it(k);

                let p = Ok(vec![p]);
                for duo in [(1, 258), (usize::MAX, 514)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let find = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, find);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn partially_shared_suffix_c_1() {
                let p = String::from("B-lyrics");
                let e = &Entry(p.as_str());

                let k = &Entry("A-lyrics");
                let mut mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e);

                let p = Ok(vec![p]);
                for duo in [(1, 132), (usize::MAX, 516)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn partially_shared_suffix_c_2() {
                let p = String::from("B-lyrics");
                let e = &Entry(p.as_str());

                let k = &Entry("A-lyrics");
                let mut mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e);
                _ = poetrie.it(k);

                let p = Ok(vec![p]);
                for duo in [(1, 258), (usize::MAX, 514)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(p, f);
                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn partially_shared_suffix_d_1() {
                let p_a = String::from("lyrics");
                let e_a = &Entry(p_a.as_str());

                let p_b = String::from("ethics");
                let e_b = &Entry(p_b.as_str());

                let k = &Entry("athletics");
                let mut mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e_a);
                _ = poetrie.it(e_b);

                let p = HashSet::from([p_a, p_b]);
                for duo in [(2, 132), (usize::MAX, 516)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(true, f.is_ok());
                    let f = f.unwrap();

                    assert_eq!(p.len(), f.len());

                    for f in f {
                        assert_eq!(true, p.contains(&f), "{f}");
                    }

                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn partially_shared_suffix_d_2() {
                let p_a = String::from("lyrics");
                let e_a = &Entry(p_a.as_str());

                let p_b = String::from("ethics");
                let e_b = &Entry(p_b.as_str());

                let k = &Entry("athletics");
                let mut mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e_a);
                _ = poetrie.it(e_b);

                _ = poetrie.it(k);

                let p = HashSet::from([p_a, p_b]);
                for duo in [(2, 258), (usize::MAX, 514)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(true, f.is_ok());
                    let f = f.unwrap();

                    assert_eq!(p.len(), f.len());

                    for f in f {
                        assert_eq!(true, p.contains(&f), "{f}");
                    }

                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn partially_shared_suffix_e_1() {
                let p_a = String::from("lyrics");
                let e_a = &Entry(p_a.as_str());

                let p_b = String::from("lodgings");
                let e_b = &Entry(p_b.as_str());

                let k = &Entry("carboniferous");
                let mut mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e_a);
                _ = poetrie.it(e_b);

                let p = HashSet::from([p_a, p_b]);
                for duo in [(2, 132), (usize::MAX, 516)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(true, f.is_ok());
                    let f = f.unwrap();

                    assert_eq!(p.len(), f.len());

                    for f in f {
                        assert_eq!(true, p.contains(&f), "{f}");
                    }

                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn partially_shared_suffix_e_2() {
                let p_a = String::from("lyrics");
                let e_a = &Entry(p_a.as_str());

                let p_b = String::from("lodgings");
                let e_b = &Entry(p_b.as_str());

                let k = &Entry("carboniferous");
                let mut mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e_a);
                _ = poetrie.it(e_b);

                _ = poetrie.it(k);

                let p = HashSet::from([p_a, p_b]);
                for duo in [(2, 258), (usize::MAX, 514)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(true, f.is_ok());
                    let f = f.unwrap();

                    assert_eq!(p.len(), f.len());

                    for f in f {
                        assert_eq!(true, p.contains(&f), "{f}");
                    }

                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn partially_shared_suffix_f_1() {
                let p_a = String::from("T-lyrics");
                let e_a = &Entry(p_a.as_str());

                let p_b = String::from("U-lyrics");
                let e_b = &Entry(p_b.as_str());

                let k = &Entry("X-lyrics");
                let mut mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e_a);
                _ = poetrie.it(e_b);

                let p = HashSet::from([p_a, p_b]);
                for duo in [(2, 132), (usize::MAX, 516)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(true, f.is_ok());
                    let f = f.unwrap();

                    assert_eq!(p.len(), f.len());

                    for f in f {
                        assert_eq!(true, p.contains(&f), "{f}");
                    }

                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn partially_shared_suffix_f_2() {
                let p_a = String::from("T-lyrics");
                let e_a = &Entry(p_a.as_str());

                let p_b = String::from("U-lyrics");
                let e_b = &Entry(p_b.as_str());

                let k = &Entry("X-lyrics");
                let mut mc = MatchConduct::test();

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(e_a);
                _ = poetrie.it(e_b);

                _ = poetrie.it(k);

                let p = HashSet::from([p_a, p_b]);
                for duo in [(2, 258), (usize::MAX, 514)] {
                    mc.max_n = duo.0;

                    let mut grade = 0;
                    let f = poetrie.find(k, &mc, &mut grade);
                    poetrie.clr_f_buffs();

                    assert_eq!(true, f.is_ok());
                    let f = f.unwrap();

                    assert_eq!(p.len(), f.len());

                    for f in f {
                        assert_eq!(true, p.contains(&f), "{f}");
                    }

                    assert_eq!(duo.1, grade);
                }
            }

            #[test]
            fn ordering() {
                let entries = [
                    "document",
                    "documentation",
                    "documentable",
                    "documented",
                    "docudrama",
                ]
                .map(rev_entry::rev)
                .to_vec();

                let key = RevEntry::new("documentational");
                let key = &key.entry();

                let mut poetrie = Poetrie::nw();
                for e in entries.iter() {
                    _ = poetrie.it(&Entry(e.as_str()));
                }

                let mut mc = MatchConduct::default();
                mc.max_n = usize::MAX;
                mc.sub_e = true;

                let proof = Ok(entries);

                let mut grade = 0;
                let mut f = poetrie.find(key, &mc, &mut grade);
                assert_eq!(proof, f);
                assert_eq!(520, grade);

                poetrie.clr_f_buffs();
                _ = poetrie.it(key);

                grade = 0;
                f = poetrie.find(key, &mc, &mut grade);
                assert_eq!(proof, f);
                assert_eq!(514, grade);
            }

            use super::super::rev_entry;
            use crate::{Find, Key};

            #[test]
            fn composite_a() {
                let mut poetrie = Poetrie::nw();

                let rev_entries = ["document", "documentalist"].map(rev_entry::rev);
                let rev_entries = rev_entries.iter().map(|x| x.as_str());

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

                let mut mc = MatchConduct::test();
                mc.sub_e = true;

                let mut ac = AssertComposite { p: poetrie, m: mc };

                let key = Entry("musics");
                let proof = String::from("physics");
                ac.assert_n(Ok(vec![proof]), 132, key, 1);

                let key = Entry("athletics");
                let proof = String::from("aesthetics");
                ac.assert_n(Ok(vec![proof]), 258, key, 1);

                let key = Entry("aesthetics");
                let proof = String::from("athletics");
                ac.assert_n(Ok(vec![proof]), 258, key, 1);

                let key = Entry("epicalyx");
                ac.assert_n(Err(FindErr::NoJointSuffix), 0, key, 1);

                let key = RevEntry::new("documental");
                let proof1 = RevEntry::new("document").0;
                let proof2 = RevEntry::new("documentalist").0;
                ac.assert_n(Ok(vec![proof1, proof2]), 130, key.entry(), 2);

                let key = RevEntry::new("documentalist");
                let proof = RevEntry::new("document").0;
                ac.assert_n(Ok(vec![proof]), 34, key.entry(), 2);

                let key = RevEntry::new("quadriceps");
                let proof = String::from("q");
                ac.assert_n(Ok(vec![proof]), 64, key.entry(), 1);

                let key = Entry("q");
                ac.assert_n(Err(FindErr::OnlyKeyMatches), 18, key, 1);

                let key = Entry("epically");
                ac.assert_n(Err(FindErr::OnlyKeyMatches), 18, key, 1);
            }

            #[test]
            fn composite_b() {
                let entries = [
                    "doctorate",
                    "doctoress",
                    "doctorfish",
                    "doctorly",
                    "doctorship",
                    "doctrinaire",
                    "doctrinal",
                    "doctrinarian",
                    "doctrinarianism",
                    "doctrine",
                    "docudrama",
                    "document",
                    "documentable",
                    "documental",
                    "documentalist",
                    "documentarian",
                    "documentarist",
                    "documentarize",
                    "documentary",
                    "documentation",
                    "documentational",
                    "documented",
                    "documenter",
                    "surge",
                    "surgeful",
                    "surgeoncy",
                    "surgeonfish",
                    "surgery",
                    "surgicenter",
                    "surging",
                ]
                .map(RevEntry::new);

                let mut poetrie = Poetrie::nw();
                for e in entries {
                    _ = poetrie.it(&e.entry());
                }

                let mut mc = MatchConduct::test();
                mc.min_sl = "doctoral".len() - 1;

                let key = RevEntry::new("doctoral");
                let proof = rev_entry::rev("doctorate");

                let mut ac = AssertComposite { p: poetrie, m: mc };
                let mut mc = ac.assert(Ok(vec![proof]), 132, key.entry());

                mc.min_sl = "doctor".len();
                mc.ext_ml = 4;
                mc.max_n = usize::MAX;

                let key = RevEntry::new("doctor");
                let proof = map_rev(["doctorfish", "doctorship"]);
                mc = ac.assert(proof, 514, key.entry());

                mc.min_sl = "doctrine".len() - 1;
                mc.max_ml = "doctrinarianism".len() - 1;
                mc.max_n = 3;

                let key = RevEntry::new("doctrine");
                let proof = map_rev(["doctrinaire", "doctrinal", "doctrinarian"]);
                mc = ac.assert(proof, 258, key.entry());

                mc.sub_e = true;
                mc.min_sl = "documental".len() - 2;
                mc.max_sl = "documental".len() - 2;
                mc.max_n = usize::MAX;

                let key = RevEntry::new("documental");
                let proof = map_rev(["document", "documented", "documenter"]);
                mc = ac.assert(proof, 514, key.entry());

                mc.min_sl = "surgeful".len();
                mc.max_sl = "surgeful".len();

                let key = RevEntry::new("surgeful");
                mc = ac.assert(Err(FindErr::DisjunctConduct), 18, key.entry());

                mc.max_n = usize::MAX;
                mc.sub_e = true;
                mc.min_sl = "document".len();

                let key = RevEntry::new("documentational");
                let proof = map_rev([
                    "document",
                    "documentable",
                    "documental",
                    "documentalist",
                    "documentarian",
                    "documentarist",
                    "documentarize",
                    "documentary",
                    "documentation",
                    "documented",
                    "documenter",
                ]);
                mc = ac.assert(proof, 514, key.entry());

                mc.max_n = usize::MAX;
                mc.sub_e = true;
                mc.min_sl = "docu".len();

                let key = RevEntry::new("documentalist");
                let proof = map_rev([
                    "docudrama",
                    "document",
                    "documentable",
                    "documental",
                    "documentarian",
                    "documentarist",
                    "documentarize",
                    "documentary",
                    "documentation",
                    "documentational",
                    "documented",
                    "documenter",
                ]);
                _ = ac.assert(proof, 514, key.entry());

                fn map_rev<const S: usize>(vals: [&str; S]) -> Result<Find, FindErr> {
                    let mut map = vals.map(rev_entry::rev);
                    map.sort();
                    Ok(map.to_vec())
                }
            }

            struct AssertComposite {
                p: Poetrie,
                m: MatchConduct,
            }

            impl AssertComposite {
                fn assert(
                    &mut self,
                    r: Result<Find, FindErr>,
                    g: usize,
                    k: Key,
                ) -> &mut MatchConduct {
                    self.assert_dynamo(r, g, k);

                    self.m = MatchConduct::test();
                    &mut self.m
                }

                fn assert_dynamo(&self, r: Result<Find, FindErr>, g: usize, k: Key) {
                    let p = &self.p;

                    let mut grade = 0;
                    let f = p.find(&k, &self.m, &mut grade);

                    if r.is_ok() {
                        let mut f = f.unwrap();
                        f.sort();

                        let r = r.unwrap();
                        assert_eq!(r, f, "g: {g}, grade: {grade}, k {k:?}");
                    } else {
                        assert_eq!(r, f, "g: {g}, grade: {grade}, k {k:?}");
                    }

                    assert_eq!(g, grade);
                    p.clr_f_buffs();
                }

                fn assert_n(&mut self, r: Result<Find, FindErr>, g: usize, k: Key, n: usize) {
                    self.m.max_n = n;

                    self.assert_dynamo(r, g, k)
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

                let trace = poetrie.btr.promote();
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

                trace.clear();
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
            fn unknown_not_path_a() {
                let entry = RevEntry::new("wordbook");
                let bad_entry = RevEntry::new("wordbooks");

                let mut poetrie = Poetrie::nw();
                _ = poetrie.it(&entry.entry());
                let res = poetrie.track(&bad_entry.entry(), false);
                assert_eq!(TraRes::UnknownForAbsentPathLinks, res);
            }

            #[test]
            fn unknown_not_path_b() {
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
            poetrie.btr.reserve(cap);
            poetrie.buf.reserve(cap);

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

                let proof_len = proof.len();
                assert_eq!(proof_len, ext.len());

                ext.sort();
                assert_eq!(proof, ext);

                let cap = ext.capacity();

                assert_eq!(true, cap >= proof_len);
                assert_eq!(true, cap < proof_len * 2);

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
        use crate::{Entry, FindErr, MatchConduct, MatchConductShaper, Poetrie};
        use std::collections::HashSet;

        #[test]
        fn sample_a() {
            let mut poetrie = Poetrie::nw();
            let words = [
                "analytics",
                "metrics",
                "ethics",
                "Acoustics",
                "antics",
                "topics",
                "anticruelty",
            ]
            .map(Entry::new_from_str)
            .map(Option::unwrap);

            for w in words {
                poetrie.it(&w);
            }

            let mc = MatchConductShaper::init()
                .max_n(usize::MAX) // unlimited matches count
                .max_sl(3) // only 'ics' or less but not '…rics'
                .max_ml(8) // only 8 or less length matches
                .form()
                .unwrap();

            let probe = Entry::new_from_str("lyrics").unwrap();
            let matchee = poetrie.sx(&probe, &mc);

            let confirmation: HashSet<String> =
                ["ethics", "antics", "topics"].map(String::from).into();

            let matchee = matchee.unwrap_or_default();
            for m in matchee.iter() {
                assert!(confirmation.contains(m));
            }
            assert_eq!(confirmation.len(), matchee.len());

            let mc = MatchConduct::default();

            let probe = Entry::new_from_str("anticruelty").unwrap();
            assert_eq!(Err(FindErr::OnlyKeyMatches), poetrie.sx(&probe, &mc));

            let probe = Entry::new_from_str("solemn").unwrap();
            assert_eq!(Err(FindErr::NoJointSuffix), poetrie.sx(&probe, &mc));
        }

        #[test]
        fn sample_b() {
            let mut poetrie = Poetrie::nw();
            let words = ["lynx", "index"]
                .map(Entry::new_from_str)
                .map(Option::unwrap);

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
