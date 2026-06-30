# Suffix Tree Concept

## Concept Basics

<ul type="square">
<li>Tree starts with rooting node, consists of branches, branches are formed by nodes, branch tip is leaf node.</li>
<li>Node can be associated to entry, but is not obligated to.</li>
<li>Entry is <i>'word'</i> present in tree, formed by branch, or its part.</li>
<li><i>Words</i> consists of <i>'letters'</i>, <i>letter</i> is arbitrary Rust <code>char</code>, <i>letter</i> is bound to node.</li>
<li>Tree is rooted in pseudo-root as this has zero association to <i>letter</i>, true roots are last <i>letters</i> of entries.</li>
<li>Leaf node is always entry node but not all entry nodes are leaf nodes.</li>
</ul>


### Simplified Branch Diagram

Diagram draws basic matching posibilites. There could be partial, whole 
or empty match to tree entry.

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
<li>Branches from main branch can but do not have to exist, similar applies for sub-entries.</li>
<li>If <i>word</i> is present as whole, it can be entry or suffix to at least one other entry, or both.</li>
<li>If <i>word</i> is present partially, it shares suffix with one or more entry or it is matched 
with its sub-entry, or both.</li>
</ul>


### Extended Branch Diagram
<pre>
       E        E
        \   E    \  E               E               E
         \ /      \/               /               /
          /       /               /               / 
        SE       /              SE      SE     WE/WN    E
|━━━━━━━|━━━━━━━|━━━━━━━|━━━━━━━|━━━━━━━|━━━━━━━|–––––––|
Lₘ       \       \              Lₜ              L₀
          \       \              \
           E       E              E
</pre>

Having word W, table below explains nodes of graph above.


| Notation | Explanation                                          |
|------|----------------------------------------------------------|
| SE   |  sub-entry, entry lying on main branch not being W-entry |
| E    |  entry, entry outside of main branch                     |
| WE   |  W is entry                                              |
| WN   |  W is not entry                                          |

---
