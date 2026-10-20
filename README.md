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
identification conflict. The static one-pass finite-block construction is now Lean-verified to
produce a full target `RoleDiary` from source V/E alone (merged #642).
The printed pre-diary lemma's universal old-cut preservation clause
remains false; the verified theorem does not establish its protected
embedding conditions or every-flip absorption.

The **verified local one-pass ingredients**, with complete Lean CI
and strict axiom reports, now include:

- `DiaryOnePassTerminalGerms`, `DiaryOnePassStaticCodeTransport`:
  fixed-first-member full pair tests factor through the later
  member's original next-cut singleton code; at the terminal cut
  the correspondence is an equivalence.
- `DiaryOnePassFinitePeeling`, `DiaryOnePassCodeEquivalence`,
  `DiaryOnePassGermSignatures`: one-hot finite child separation,
  exact correspondence of finite singleton/full-pair codes to
  source types, finite realised normal/terminal germs (including
  the unique terminal pair child per parent).
- `DiaryPrediaryRoleNextCut`, `DiaryOnePassOriginalSplitWitness`:
  source V/E-only old 1-/2-split successor-cut identities,
  witness-based strict child separation, and their finite-code
  statements. These theorems do not assume S1/S2 of an already
  completed diary.
- `DiaryExactS2Cap`, `DiaryOnePassNoRedundantEvents`: the exact
  manuscript S2 alternative under S1 and the absence of
  unnecessary events when the input is already a diary.

The **concrete carrier stage** is also now checked (merged #558–#561):

- `DiaryOnePassFiniteSchedule`: realised original singleton/pair
  parent-child fibres, selected finite event blocks, terminal-child
  defaults, strictly increasing original-vertex indices, and fixed
  initial markers 0,1,2.
- `DiaryOnePassConcreteCarrier`: a concrete inserted-edge predicate
  supported only at fresh event positions and an induced embedding
  reflecting every original edge AND nonedge.
- `DiaryOnePassRawEdgeShapes`: strictly increasing support for every
  target edge under original V/E, declared new split incidences,
  and exact preservation/reflection of old role marker edges.
- `DiaryOnePassLexRanking`: singleton children sorted by decreasing
  binary source-type rank, with the least normal child (or terminal
  child if present) serving as default. This is the required event
  ordering rule; the correspondence to final target V3 still needs
  the global finite-cut transport proof.

The **local two-way target transport ingredients** are now also
CI-verified (merged #562, #564–#567):

- `DiaryOnePassRealisedClassSeparation` (#562): a family of selected
  original germ class tests distinguishes precisely the realised
  normal/terminal singleton/full-pair children within each parent.
- `DiaryOnePassEventReflection` (#564): event positions are globally
  unambiguous; an actual new singleton/pair event edge exists **iff**
  the original leaf or ordered leaf pair belongs to its selected
  full source germ class. No off-block or wrong-arity edge interferes.
- `DiaryOnePassSelectedEventRealization` (#565): every selected source
  singleton/pair germ is represented by a real vertex in the ordered
  finite block. Sorting singleton children loses no events.
- `DiaryOnePassDelayedPairGermFactor` (#566): when an earlier pair
  event is later tested as a singleton coordinate at original leaf
  q, its actual edge incidence is constant on every original
  singleton type class through q+1, including terminal caps.
- `DiaryOnePassTargetEventPartition` (#567): for source leaves or
  ordered leaf pairs with the same original parent type, agreement
  of their **actual target event edges** is equivalent to equality
  of their normal/terminal source refinement germs.

### Current concrete one-pass validation (17 October 2026)

The actual target carrier now has complete verified **E1–E5** permitted
edge shapes and literal role coverage (merged #568–#572). Finite
event-block bounds and the old/event target vertex equivalence are
checked (#573–#574). The exact marker-cut base, original split
successor identities and actual full-block event-test decompositions
are checked (#575–#581).

The major **two-way global transport** results are verified:

- `DiaryOnePassGlobalOneTypeTransport` (#586) preserves AND reflects
  source singleton-type agreement at the **start** of each original
  event block, on source leaves at or above that original cut.
- `DiaryOnePassGlobalTwoTypeTransport` (#590) proves the analogous
  statement for full ordered-pair types, including both singleton
  coordinates and auxiliary pair-edge tests.
- The delayed original leaf-column, selected-germ partition,
  normal/terminal capped pair, and copied old split cases are
  checked, without source S1/S2 (#582 was superseded by #584).

The **V-axiom validation** has also advanced:

- `DiaryOnePassTargetLeafCones` (#591) proves every target leaf is
  an image of an original leaf, with exact positive event cones.
- `DiaryOnePassTargetV1Coherence` (#592) and
  `DiaryOnePassTargetV2Coherence` (#595) verify the positive-leaf
  and positive-pair coherence fields for ALL actual target splits.
- `DiaryOnePassOldSplitWitnessTransport` (#594) preserves exact
  witness meets at original splits. Real selected/default germ
  children and block label uniqueness are checked (#596–#599).
- `DiaryOnePassFreshOneMeet` (#601) and
  `DiaryOnePassTargetV1Witness` (#602) now prove the exact witness
  meet at every fresh singleton event and the complete target
  **V1 witness** axiom.

- `DiaryOnePassPairEventOrder` (#603),
  `DiaryOnePassDefaultPrePairEventAgreement` (#604),
  `DiaryOnePassFreshTwoMeet`, and
  `DiaryOnePassTargetV2Witness` (#605) prove the genuine
  pair-event-before-singleton schedule, before-event selected/default
  agreement, exact fresh numerical pair meet and the complete target
  **V2 witness** axiom. All are merged and CI/axiom-audit green.
- `DiaryOnePassV3Reduction` (#608) proves **both** target Devlin
  marker clauses if and only if source `LexEarlier` is preserved on
  original leaves. This is a two-way reduction, NOT preservation.
- `DiaryOnePassFreshLexOrientation` (#609) proves exact
  selected/default fresh-singleton orientation from the original
  full two-type meet definition.
  `DiaryOnePassLexRankSort` (#610) verifies weak descending
  numerical germ ranks in the actual finite singleton list.
  `DiaryOnePassTwoSelectedLex` (#611) proves exact first meet and
  target orientation for two actual selected sibling children.
  These are all merged with green Lean builds and strict axiom audits.

The **actual one-pass target is now a verified diary**, with green Lean
CI and strict axiom audits (17 October 2026):

- `DiaryOnePassGlobalV3` (#633) gives unconditional source leaf
  `LexEarlier` preservation and both target V3 Devlin marker clauses.
- `DiaryOnePassTargetPrediary` (#634) packages the complete target
  V/E pre-diary axioms.
- `DiaryOnePassTargetS1` (#638) and `DiaryOnePassCompleteS2` (#642)
  establish target S1, target S2 and
  `onePassRawTarget_isDiary : RolePrediary H → RoleDiary (onePassRawTarget H)`,
  without source S1/S2.
- `DiaryProtectedMixedEdgeShapes` (#643) eliminates positive
  auxiliary incidences for pairs containing splits and late singleton
  tests ending at splits. `DiaryProtectedMixedTypeTransport` (#644)
  transports full two-type agreement at corresponding original block
  cuts when mixed pairs have aligned coordinate roles.

### Verified relative finite protected completion (18 October 2026)

The following additional modules are green in Lean CI with strict axiom
reports. They **do not** assume source S1/S2 beyond explicitly stated
protected comparisons:

- `DiaryProtectedMixedNumericalMeets` (#645) preserves exact auxiliary
  numerical meets of split-containing pairs; `DiaryProtectedSplitSingletonMeets`
  (#647) preserves singleton numerical meets involving split endpoints.
- `DiaryProtectedMixedFullMeets` (#648) combines those results with
  original 1-split leaf meets to preserve full two-meets when both
  ordered pairs contain splits and their coordinate meets are protected.
- `DiaryProtectedLeafTwoMeets` (#649) handles all-leaf pairs, including
  genuine common-first-leaf caps, and
  `DiaryProtectedCrossRolePairMeets` (#651) handles a split-containing
  pair versus an all-leaf pair using the early Devlin markers.
- `DiaryFiniteProtectedMeetPicture` (#652) packages the finite
  nonmarker S1/S2 meet conditions into an actual induced old-copy
  embedding preserving **every singleton and ordered-pair numerical
  meet within that finite set**. Any finite set of nonmarker vertices
  in a full RoleDiary satisfies its hypotheses.
- `DiaryFiniteProtectedWithMarkers` (#653) extends this verified
  relative meet preservation to the marked finite picture including
  the distinguished vertices 0,1,2.

**Scope:** the source is an ambient V/E `RolePrediary` on Nat and the
finite subset is *already protected* there in the exact restricted
S1/S2 numerical-meet sense. The output is a completed countable
`RoleDiary`, with a finite induced protected image; this does not
by itself produce an independently finite diary satisfying finite
split-witness clauses.

The printed universal old-cut type-agreement preservation clause is
**false** and has not been reinstated. The manuscript's independent
ordered-sum note proposes joint embedding of finitely many flips,
conditional on constructing and protecting the appropriate ambient
pre-diary. It does not solve absorption into EVERY flip of the target.

### Verified finite leaf-meet diary extraction (20 October 2026)

The genuine **finite diary output**, not merely a countable completion,
has now been checked on main. For any countable `RoleDiary G` and any
finite set `L` of its genuine leaves, the generated support consists
of markers 0,1,2, `L`, distinct-leaf singleton meets, and all full
ordered-pair meets of leaf pairs from `L`. Increasing induced
reindexing gives a **`FiniteRoleDiaryBlock`**, exported as
`DiaryLeafPriority.finiteLeafMeetSupport_is_finiteDiary` in
`DiaryFiniteLeafMeetCompleteReduct.lean` (merged PR #747).

The theorem uses checked support provenance and S1/S2 (#727–#736),
bounded role coverage (#739), positive-class V1/V2 coherence and
all E1–E5 forms (#742), both retained V3 Devlin marker laws (#744),
and exact bounded V1/V2 split witnesses (#747). Complete Lean CI,
strict transitive axiom reports, and finite regressions passed on
the final integrated PR head.

### Verified finite protected factorisation and finite-family joint embedding (20 October 2026)

The missing finite protected-copy factorisation is now Lean verified
(merged PR #755, green integrated Lean CI and strict axiom audit).

- `FiniteMeetEmbedding.through_finiteSupport` sends a genuine finite
  meet embedding through any finite increasing induced support
  containing its full source image. It preserves ALL numerical
  singleton and full ordered-pair meets, including mixed split/leaf
  tuples. Exact first-difference witnesses are retained in the image;
  no false backwards transport of arbitrary ambient type tests is used.
- `FiniteMeetEmbedding.factor_through_leafMeetSupport` combines this
  with the extracted `FiniteRoleDiaryBlock`. It produces a
  **genuinely finite** target diary with a fully protected input copy.
- `exists_finiteDiary_for_finiteFamily` gives one finite diary
  jointly containing any finite family of finite diary inputs, all
  by induced, marker- and mixed-meet-preserving embeddings.

**Still open:** the MUCH STRONGER assertion that **every flip of the
finite target** contains the prescribed source diary; and the final
diary unavoidability conclusion. Ordinary finite joint embedding
of all flips of the source DOES NOT imply this absorption property.
The V2 shared-root obstruction rules out the raw chronological
flip-prefix amalgam. The original generic cut-zero orientation lemma
as worded is not certified merely by the alternative four-tail proof.


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
