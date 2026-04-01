# Tree Concept

## Concept Basics

<ul type="square">
<li>Keys are entries of tree, tree consists of branches, branches are formed by nodes.</li>
<li>Node can be associated to entry, but does not have to.</li>
<li>Keys can be referred to as <i>'words'</i>, but not all <i>words</i> are keys.</li>
<li><i>Words</i> consists of <i>'letters'</i>, <i>letter</i> is arbitrary Rust <code>char</code>, <i>letters</i> are bound to nodes.</li>
<li>Tree is rooted in pseudo-root, it has zero association to <i>letter</i>, true roots are last <i>letters</i> of keys.</li>
<li>Leaf node is always entry node but not all entry nodes are leaf nodes.</li>
</ul>


### Simplified Branch Diagram

<pre>
                   l 
|━━━━━━━━━━━━━━━━━━━━|━━━━━━━━━━━━━━━━|
Lₘ                   Lₜ               L₀
</pre>

- Lₘ — last <i>letter</i> of <i>word</i>, true tree root
- Lₜ — topmost <i>letter</i> of <i>word</i> present in tree
- L₀ — first <i>letter</i> of <i>word</i>, it is identical with Lₜ for t = 0
- l  — main branch, branch with match to <i>word</i>

---

## Verity Extension

<ul type="square">
<li>Each and every node can participate in multiple branches.</li>
<li>Entry node on main branch not being L₀ node is sub-entry node.</li>
<li>If main branch can be extended, it is branching on L₀ node.</li>
<li>Branches from main branch can or do not have to exist, similar applies for sub-entries.</li>
<li><i>Word</i>  can be present in tree partially or whole.</li>
<li>If <i>word</i> is present as whole, it can be key or suffix to at least one other key, or both.</li>
<li>If <i>word</i> is present partially, it shares suffix with one or more keys or it is matched 
with its sub-key, or both.</li>
</ul>


### Nodes Detail Diagram
<pre>
       E        E
        \   E    \  E               E               E
         \ /      \/               /               /
          /       /               /               / 
        SE       /              SE      SE     W/KE     E
|━━━━━━━|━━━━━━━|━━━━━━━|━━━━━━━|━━━━━━━|━━━━━━━|–––––––|
Lₘ       \       \              Lₜ              L₀
          \       \
           E       E
</pre>
        
- SE — sub-entry, entry lying on main branch not being key-entry
- W  — word, word is present in tree
- E  — entry, entry outside of main branch
- KE — key-entry, word is key

---
