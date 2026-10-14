# lean-3-uniform-diaries

Lean formalisation accompanying the 3-uniform diaries manuscript. The finite auxiliary type-respecting Ramsey statement has a verified
unconditional formalisation, together with its `K_I` embedding and
concrete scalar coding arguments. Other manuscript statements require
separate source-level audits.

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
- The concrete nonuniformly branching scalar strong-tree model and
  its finite image code, with a direct application of the reusable
  `Milliken.GeneralTree.millikenFixedStemFiniteColouring_of_boundaryProductHL`
  theorem. The general-tree Halpern–Läuchli input is discharged by
  `boundaryProductHL_unconditional`.
- The unconditional finite auxiliary type-respecting Ramsey property,
  including the incompatible-prefix case, is exported as
  `ThreeUniformDiaries.ATRFiniteDecoder.actualFiniteAuxRamsey_allFinite`.
  This proof does not assume a synthetic scalar-realisation record,
  a fixed branching alphabet or an unproved Halpern–Läuchli property.

## Unconditional finite Ramsey theorem and upstream library

The root-glued E0/E1/E2 scalar tree is a genuinely pruned, locally
finitely branching `Milliken.AmbientTree` whose degree need not
be globally bounded. Its selected ranks, strong subtrees, finite
approximation decoders and the fixed outer self-embedding are
formalised in the concrete diary modules.

The source of the combinatorial Ramsey input is
[lean-milliken](https://github.com/janhubicka/lean-milliken), whose
theorems concern arbitrary ambient rooted trees independently of
this application. The diary project imports these mathematical
interfaces directly; it does not re-export the library's generic
finite-colouring lemmas or maintain conditional compatibility adapters.

For the finite induced auxiliary embeddings considered here, the
main application proceeds via the following checked stages:

1. A genuine finite-image scalar colour on `r_(k+2)(X)` is constructed
   from the selected canonical branch decoder.
2. The general fixed-stem Milliken implication from boundary product
   Halpern–Läuchli homogenizes that colour on a protected strong
   refinement of the root-glued ambient tree.
3. A single uniform type-respecting self-embedding of the generic
   3-hypergraph is constructed before quantifying over finite images.
   The genuine finite-image branch comparison identifies its colours.
4. The unconditional boundary product HL theorem discharges the
   combinatorial input, and the incompatible fixed-prefix case is
   handled separately.

The proof-integrity audit is in `scripts/CheckAxioms.lean`.
The project remains under mathematical audit in parts not covered by
this finite theorem; a successful Lean build must not be interpreted
as validating a stronger unexported manuscript statement.

## Removed historical adapters

The preceding proof once passed through several conditional
`ATRGeneralMilliken` and `ATRScalarRealization` bridge modules and
a local wrapper around a generic Ramsey-space colouring lemma.
Those modules have been retired in favour of the verified direct
general-tree theorem API. The concrete coding and finite-image
realisation arguments are retained.

## Repaired C2 induction

GapCounterexample.lean disproves the earlier blanket
zero-on-omitted-pairs recurrence by a finite capped-meet failure.
The repaired rule copies omitted pair bits below the immediate
parent image and zeros them at or above the parent. The full
fixed-prefix and root-based K_I branch verifications now establish
that the **repaired** induction preserves exact meets. The
counterexample concerns the obsolete rule, not the Ramsey statement.
