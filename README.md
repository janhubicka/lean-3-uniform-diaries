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

## ATR application status (12 October 2026)

The proof of the **conditional final Ramsey transfer** is checked. The genuine
three-coordinate E0/E1/E2 strong picture glues to the actual nonuniformly
branching `Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree`.
Its predecessor/meet geometry, finite local branching, ambient rank, exact
scalar source levels, and the equality of scalar finite approximations with
the glued coordinate prefixes are checked without any global degree bound.

`ATRGeneralMilliken.ATRScalarRealization.atrRamsey_of_boundaryProductHL`
is checked assuming exactly two explicit inputs: the concrete decoding /
realization data `ATRScalarRealization` and the upstream heterogeneous
Halpern–Läuchli assumption `HasBoundaryProductHL`. The general A.1–A.3,
Tychonoff closedness, abstract A.4 reduction, and final finite-colour
deduction are checked; **the boundary HL input remains unproved in
the pinned upstream repository**. No theorem should be marked green solely
because this conditional implication compiled.

## Remaining Ramsey theorem obligations

1. Prove the reverse scalar-to-vector strong-subtree correspondence for
   actual E0/E1/E2 coordinate slices, with the protected initial segment.
   The forward correspondence and exact finite-prefix equality are checked.
2. Construct the actual finite-code decoder and the realization law for
   refined strong pictures, using the already checked Aemb finite code,
   strong completion, selected-level prefix, and infinite canonical
   composition. Instantiate `AuxRamseyCoding` with the actual K_I branch
   action and universal embedding, rather than merely a generic record.
3. Import the unconditional heterogeneous boundary-product HL / Milliken
   theorem from `lean-milliken` once that proof is completed, verify its
   exact hypotheses on the actual glued ambient tree, and eliminate the
   last explicit theorem assumption.
4. Instantiate the final theorem with the geometric and coding data and
   audit transitive axioms. Until then the manuscript ATR theorem remains
   partially validated.

## Repaired C2 induction

GapCounterexample.lean disproves the earlier blanket
zero-on-omitted-pairs recurrence by a finite capped-meet failure.
The repaired rule copies omitted pair bits below the immediate
parent image and zeros them at or above the parent. The full
fixed-prefix and root-based K_I branch verifications now establish
that the **repaired** induction preserves exact meets. The
counterexample concerns the obsolete rule, not the Ramsey statement.
