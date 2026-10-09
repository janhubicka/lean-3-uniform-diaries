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
- A checked finite-colour Milliken consequence for homogeneous trees
  and the conditional final Ramsey transfer through K_I
  (MillikenFiniteColour, AuxRamseyTransfer).

## Remaining Ramsey theorem obligations

1. Construct the **concrete canonical maps** from strong vector
   subtrees of the three type trees, and check Lemmas canonical,
   auxtypeemb and canonicalcomposition at that concrete interface.
2. Verify the **finite strong-tree encoding** in manuscript Lemma
   Aemb: the three meet-closed sets of enumeration/1-type/aux-type
   nodes, their completion to synchronized strong subtrees, and the
   precise finite encoding identity.
3. Connect the actual finite, finitely branching **vector Milliken**
   theorem to the existing homogeneous-tree Lean dependency. The
   checked `homogeneousMillikenFiniteColouring` alone is not a
   verification of the vector-tree statement in the manuscript.
4. Instantiate the existing `AuxRamseyCoding` transfer with those
   constructions and obtain the unconditional Ramsey theorem.

The distinction between a checked conditional deduction and a checked
unconditional theorem is intentional; do not mark manuscript
Theorem ramsey fully verified until these obligations are discharged.

## Repaired C2 induction

GapCounterexample.lean disproves the earlier blanket
zero-on-omitted-pairs recurrence by a finite capped-meet failure.
The repaired rule copies omitted pair bits below the immediate
parent image and zeros them at or above the parent. The full
fixed-prefix and root-based K_I branch verifications now establish
that the **repaired** induction preserves exact meets. The
counterexample concerns the obsolete rule, not the Ramsey statement.
