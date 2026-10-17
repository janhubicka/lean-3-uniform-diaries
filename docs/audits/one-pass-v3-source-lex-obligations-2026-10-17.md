# One-pass V3: source lex comparison and event scheduling

Status: **English reduction and adversarial audit only** (17 October 2026).
No statements in this note should be counted as Lean-verified unless an
explicit theorem and green PR are cited. The manuscript circulation prose
remains frozen.

## Verified input

* The source pre-diary has V/E, not S1/S2. The actual target is a
  one-pass finite-block enumeration with induced old edges.
* Exact source-to-target singleton and full pair-type transport
  holds at the **start** of each original block (Lean #586, #590),
  not at arbitrary old-image indices.
* Original and fresh target V1/V2 coherence and witnesses are complete
  (#592, #595, #602, #605), without assuming target diary axioms.
* Target leaves are precisely images of old leaves (#591).
* Complete target V3 is equivalent to old-leaf `LexEarlier`
  preservation (#608); this **does not** prove preservation.
* A selected child is lexicographically **after** its unselected
  default sibling (#609). The actual selected list has weak
  descending binary ranks (#610). If two same-parent selected
  singleton events occur at indices `i < j`, their leaf
  representatives have exact target one-meet at `i` and the earlier
  selected child is lexicographically after the later one (#611).

## Source rank orientation: precise remaining lemma

For distinct *source leaves* `u,v`, let
`m := H.oneMeetLevel u v`. The proposed source-code lemma is

```lean
-- OPEN, NOT A THEOREM YET
LexEarlier H u v ↔
  oneGermBinaryRank m (oneGermCode H m u) <
  oneGermBinaryRank m (oneGermCode H m v)
```

This requires showing `m ≥ 3` and that the two germ parent codes
are identical. If `m = min u v`, the smaller enumerated leaf is
the terminal child, rank zero, and its distinct normal sibling has
positive rank. For `m < min u v`, the source singleton types agree
below `m` and first disagree at successor cut `m+1`. Their
first differing test is `(q,m)`, with `q < m`. The auxiliary meet
of the mixed pairs `(m,u),(m,v)` is exactly `q`, and the
full mixed pair meet is also `q`. By the **actual manuscript
definition**, `LexEarlier H u v` is exactly the bit
`H.edge q m v`. The equal-length successor singleton words
enumerate tests first by their second coordinate and then by the
first. Therefore a valid big-endian binary rank comparison must
read the same first differing bit.

This is an English proof outline, not yet a Lean-certified
equivalence. Check carefully the decomposition of full mixed pair
meets, the capped case and the source parent-code equality.

## How it should imply global target V3

Let `m` be the source first singleton divergence of `u,v`.

1. At an original 1-split, the unchanged old split edge makes the
   same orientation in the target; no singleton events are inserted
   into its block. Formalize the exact first-meet transfer for
   **these particular leaves**, not the known-false universal old
   cut-preservation claim.
2. At an original leaf, the source germs have the same parent and
   distinct successor children. At least one is selected. A selected
   germ versus the default is handled by #609. Two selected germs
   are ordered in the block by decreasing rank, so their target
   comparison follows from #611. Terminal germs must be handled
   as actual default children.
3. At an original 2-split the permitted-edge shapes supply no
   new singleton middle-coordinate test, so it cannot be the first
   one-type disagreement. Verify this using the **source** V/E
   assumptions only.
4. Global pre-block type transport (#586) excludes an earlier
   separating target event. Arbitrary pair-event ordering is safe
   only because such events do not appear as singleton tests at
   their own block and the delayed old leaf-column test factors
   through the next source singleton type (the checked T1 case).

## Independent adversarial checks

* **Rank collision:** do not infer that the rank map is injective
  over *all* germs (parent types can differ, and terminal/rank
  conventions matter). Prove strict rank distinction only for
  different **same-parent** successors; binary words have equal
  length there. An event list that merely has `Pairwise ≥` does
  not settle ties.
* **Wrong cut:** the global transport theorems compare source cut
  `m` with the start `onePassBefore H m`, not the cut after
  `onePassOldImage H m`. The latter is false without extra
  restrictions.
* **Wrong orientation:** `LexEarlier H u v` reads the right
  full-mixed-meet edge, not simply the first obvious
  `(0,m,v)` edge at a source split. Only the fresh event
  discrepancy in #609/#611 forces that mixed meet to zero.
* **Delayed pair tests:** an inserted pair event may appear earlier
  than a later old singleton test as an *auxiliary* edge; show it
  cannot become the first singleton disagreement before the
  earlier scheduled singleton split.
* **Scope:** obtaining the V3 field does NOT establish S1/S2,
  protected mixed meets, finite-diary completion or simultaneous
  embeddings into every flip of the completed target.

## Next Lean milestones

First prove fixed-length Boolean-word binary rank faithfulness,
source `LexEarlier` versus first-different-word/rank for any
two source leaves, and the event-index strict-rank ordering
within a parent. Next combine these with #609/#611 and global
transport to derive `OnePassPreservesSourceLex`, then apply #608.
Only after that attempt source V/E to target S1/S2 and the
separate protected flip-absorption construction.
