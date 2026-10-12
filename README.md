# lean-3-uniform-diaries

Lean formalisation accompanying the 3-uniform diaries manuscript. The
auxiliary type-respecting Ramsey theorem itself is **not yet fully
formalised**. Its difficult generic K_I embedding lemma now is.

## Verified components

The imported modules on main build in CI. The principal exported
theorems are checked in scripts/CheckAxioms.lean; no `sorry` or
`admit` is permitted by CI.

- Three finite type trees (enumerations, singleton types and
  auxiliary types), their successor decompositions, and representation
  by edge-agreement predicates (TypeTrees, TypeRepresentation,
  AgreementSuccessors, AuxTypes).
- Generic initial-segment and branch coding, size-first K_I
  enumeration and literal prefix/parent schedule
  (RelativeBranchHypergraph, BranchCutBoundary, SizeFirstEnumeration,
  SizeFirstSourceTests, SizeFirstParentSchedule, SizeFirstFixedPrefix,
  FixedPrefixParentSchedule).
- Predecessor-relative C1/C2 construction, with omitted-target copy
  and zero rules both in root and fixed-prefix versions
  (InheritedGapExtension, FixedPrefixCountableEmbedding,
  FixedPrefixGlobalGap, FixedPrefixBranchGap).
- **The complete indexed K_I embedding lemma:** root-based and fixed
  prefix canonical branches preserve singleton and auxiliary types
  and their exact capped meets (RootBranchExactMeets,
  FixedPrefixBranchAuxEmbedding). A single global K_I embedding works
  for every H extending the prescribed I, including n=0, as proved
  in `exists_universal_exactMeetEmbedding`
  (UniversalAuxBranchEmbedding). The finite zero-extension corollary
  is `EnumNode.exists_finite_auxTypeEmbedding`
  (FiniteAuxBranchEmbedding). These correspond to manuscript
  Lemma Kiemb and its generic embedding corollary.
- Algebraic properties of abstract canonical maps, including
  composition and selected-cut type agreement (CanonicalMap,
  CanonicalAgreement).
- A checked finite-colour and fixed-stem Milliken consequence for homogeneous
  trees, now imported directly from the published `lean-milliken` application
  API and re-exported by thin compatibility wrappers; and the conditional
  final Ramsey transfer through K_I (MillikenFiniteColour,
  MillikenAnchoredFiniteColour, AuxRamseyTransfer).

## The final Milliken application (12 October 2026)

The CI-verified conditional application has now been merged as
`ATRGeneralMilliken` and `ATRScalarMillikenTransfer`. The
`ATRBoundaryMillikenApplication` module (on its integration branch)
eliminates two artificial application hypotheses: arbitrary-tree A.4
and Tychonoff closedness follow from the `lean-milliken` library
under the one precise boundary-product HL condition.

`ATRScalarRealization.atrRamsey_of_boundaryProductHL` consequently
has exactly two mathematical proof inputs, both visible in its type:
`HasBoundaryProductHL U` and `ATRScalarRealization C U`. It does
**not** claim an unconditional proof of manuscript Theorem ramsey.
The original finite-subtree/strong-refinement realization theorem in
`lean-milliken` PR #92 is now checked and merged, removing that
separate possible gap in the use of Milliken 1979.

## Remaining Ramsey theorem obligations

1. Build a genuine `Milliken.AmbientTree` from the root-glued
   E0/E1/E2 type forests, including the rooted meet/order and predecessor
   data. Their direct carrier, level, finite-child, and pruning
   properties are already checked. A bare meet-preserving encoding
   is insufficient.
2. Construct the **concrete** `ATRScalarRealization` and the
   corresponding `AuxRamseyCoding` instance, including both directions
   of the strong vector/scalar correspondence, fixed-stem decoding,
   and realization of every refined finite code. Much of the finite
   completion and genuine infinite canonical-map composition has
   already been proved in separate modules.
3. Supply an actual proof of heterogeneous boundary-product
   Halpern--Läuchli (`HasBoundaryProductHL U`) for the constructed
   ambient tree, or import a genuinely unconditional general-tree
   theorem once available. The upstream theorem presently remains
   conditional at precisely this interface; there is no global
   uniform branching bound.
4. Apply the checked final theorem to those concrete objects and
   upgrade the manuscript validation marker only after the unclosed
   inputs disappear from the type.

## Repaired C2 induction

GapCounterexample.lean disproves the earlier blanket
zero-on-omitted-pairs recurrence by a finite capped-meet failure.
The repaired rule copies omitted pair bits below the immediate
parent image and zeros them at or above the parent. The full
fixed-prefix and root-based K_I branch verifications now establish
that the **repaired** induction preserves exact meets. The
counterexample concerns the obsolete rule, not the Ramsey statement.
