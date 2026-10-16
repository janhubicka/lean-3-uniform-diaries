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

## Lower-bound diary and flip interfaces

The **countable, role-based V/E/S diary** lower-bound route has
additional verified results on `main`. Their scope is important:

- `DiaryCompleteNativeStabilisation` exports the actual finite-source
  I1/I2/I3 stabilisation statement after the unordered outer map is
  made increasing. Every ATR colouring acts on genuine finite images,
  not on an arbitrary infinite zero-extension.
- `DiaryFourTailGenericRealization`,
  `DiaryFiniteThreeTailShiftATR`,
  `DiaryFourTailCommonFiniteCodes`,
  `DiaryFourTailOppositeI3`, and
  `DiaryNativeOppositeTargetOrientation` construct a common four-tail
  source for opposite diary leaf-pair classes, show both three-tail
  inclusions are **finite auxiliary-type-respecting**, and transfer
  opposite target orientations through native I3. Inserted target
  levels are not assumed convex.
- `DiaryGlobalOrientationFromFourTail` proves the relative
  orientation pattern and the single global preserve/reverse sign for
  ordered diary leaf pairs.
- `DiaryUnconditionalPreembedding` exports
  `RoleDiary.exists_preembedding_into_leaf_range`. Given an unordered
  generic-to-target hypergraph embedding whose images are target
  leaves, it constructs an increasing diary pre-embedding satisfying
  the full role/leaf-meet specification, with its leaf images inside
  the original outer embedding's range.
- `DiaryFlipLocalIncidence`, `DiaryFlipOneSplitControl`,
  `DiaryFlipTwoSplitControl`, `DiaryFlipRoleReflection`,
  `DiaryFlipPrefixReconstruction`, and
  `DiaryFlipOriginalBitEquivalence` verify the local flip bit
  reconstruction. The controls really are the manuscript's
  source-positive deleted-edge bits; agreement before a cut gives
  literal agreement of the two flips' initial finite pictures.
- `DiaryFlipBranchAmalgam` builds the **induced relational
  prefix-tree** of flip branches and proves a conditional
  cross-branch nonedge obstruction. `DiaryFlipFiniteLevels` shows
  every depth and every bounded initial collection of candidate
  nodes is finite, independently of the number of flip branches.
- `DiaryFlipSingleBitPrefix` proves that the corrected
  role-restricted one-/two-split controls pack into precisely
  **one Boolean flip bit per source level**. The manuscript's
  one-bit prefix and the former two-control node have identical
  equality relations, and every branch shares the three marker
  levels. Importantly, deleted Devlin edges at markers are *not*
  independent flip controls.
- `DiaryFlipCrossBranchExtension` permits extra edges only on
  increasing-level triples not wholly spanned by any branch,
  preserving all branch edges **and nonedges**. It supplies no
  cross-branch coherence rule on its own.
- `DiaryPrediaryInsertionInvariant` verifies that insertion of
  a new level, with arbitrary new edges only involving that
  level, keeps the old hypergraph as an induced, order-preserving
  copy, and preserves the exact singleton, auxiliary and full
  pair-type equalities **below the insertion cut**.
- `DiaryPrediaryTypeCode` proves a complementary Boolean-code
  lemma at **fixed old later cuts**: if the newly inserted bit
  factors through the old next-level type, prefix-type equality
  is unchanged after shifting the cut. The accompanying
  two-point counterexample shows why factorisation cannot be
  omitted. The actual V/E insertion must still be connected
  to this abstract code and a strictly progressing finite
  original-prefix measure.

**An additional obstruction to the raw flip tree:** the issue is
not only missing Devlin edges between incomparable leaves.
`DiaryFlipRootTypeObstruction` proves the V2 fact that positively
incident leaf pairs at a shared 2-split must agree on their
marker-1 auxiliary bit. The manuscript note
[`flip_root_obstruction_and_ordered_sum.tex`](https://github.com/janhubicka/3-uniform-diaries/blob/main/notes/flip_root_obstruction_and_ordered_sum.tex)
exhibits two explicit genuine nine-vertex flips with a shared
chronological prefix through source level 3 but OPPOSITE marker-1
bits on pairs positive at that source 2-split. Consequently no
addition of off-branch edges can make their induced
chronological prefix union a pre-diary without changing its
split-node identifications. The root must already encode some
future positive-type information.

The verified cross-branch marker-complement interface
(`DiaryFlipCrossBranchMarkers`, merged #535) and old-type
class-indicator interface (`DiaryPrediaryClassIndicators`,
merged #534) remain useful, but they cannot repair this V2
identification conflict. A separate English one-pass finite-block
pre-diary completion proof is recorded in the manuscript repository;
the printed pre-diary lemma's universal old-type agreement clause
is false, and the corrected theorem is not yet Lean-verified.
The manuscript note also gives a protected ordered-sum amalgam
for finite families of diaries, conditional on the relative
completion proof, which addresses only the FIRST finite flip
joint-embedding direction.

**Still pending:** a redesigned flip-absorbing construction satisfying
the EVERY-flip-of-the-target direction, compatible protected
cross-branch structure, a formal finite-diary interface,
the corrected one-pass completion theorem, the original generic
cut-zero orientation lemma as worded, and final diary
unavoidability. No component should be cited as validation
of these stronger claims.

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
