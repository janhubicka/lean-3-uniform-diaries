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

**Resolved by 29 October 2026:** the stronger assertion that EVERY
genuine flip of one finite target embeds the original source is now
proved by the causal sign-rooted construction
(`exists_finiteDiary_strong_both_flip_directions`, merged PR #952).
Ordinary finite joint embedding alone would NOT have implied it:
the proof separately establishes cross-branch two-split meets
and injectivity of the concrete geometric feedback. The V2
shared-root obstruction still rules out the old chronological
raw prefix-tree argument. Final diary unavoidability and the
original generic cut-zero orientation statement are separate.



### Canonical flip-feedback repair and finite separation test (21 October 2026)

The previous feedback reduction was **incorrect as a route to
injectivity** because raw `FiniteDiaryEdgeCode n` tables include
non-increasing triples discarded by `finiteDiaryCodeGraph`.
`DiaryFiniteRawCodeCollision` proves in Lean that toggling just
the (0,0,0) bit creates a distinct valid raw flip code for the
same diary. For EVERY choice of protected copies, the old
`realizedSourceFlipFeedback` is therefore **noninjective even
when the target flip is the identity**. Its universal-injectivity
hypothesis cannot hold. This is a counterexample to the raw-code
representation, not to the mathematical flip-property statement.

The repaired `DiaryFiniteCanonicalSourceFlipOrbit` retains only
normalized codes satisfying encode(decode(code)) = code.
Every genuine source flip has its unique canonical code.
`DiaryFiniteCanonicalRealizedFeedback` constructs the actual
geometric feedback on this finite orbit and verifies it is
**exactly the identity** under the identity target flip,
independently of the chosen protected embeddings.

`DiaryFiniteCanonicalFeedbackReduction` proves the corrected
conditional bounded absorption statement. The finite collision
test in `DiaryFiniteCanonicalFeedbackCollisionCheck` reduces its
remaining geometric injectivity hypothesis to a check of
pairwise distinct pulled-back edge tables for all canonical
source flip codes and the finite set of realisable target flip
codes. This is a correct finite certificate, NOT evidence that a
suitable coherent copy family exists for every diary.

**Resolved in PR #952:** the required finite every-target-flip
absorber exists for every source diary. The earlier multivalued
positive-anchor covering criterion remains valid, but the final
proof uses the concrete sign-rooted copies, the first differing
genuine E3 witness bit, and its preserved cross-branch meet.
No independent Boolean flip coordinates or arbitrary
Classical.choose maps are substituted. The manuscript
circulation text remains frozen.


### Verified positive-anchor flip covering and constrained finite signatures (23 October 2026)

These 23 October component results were merged on Lean `main`
with full builds, strict transitive axiom audits and finite regressions.
Taken alone they did NOT construct a general absorber; the subsequent
sign-rooted geometry and cross-branch meet transport do so in PR #952.

- `DiaryFinitePositiveAnchorCompletion` and
  `DiaryFinitePositiveAnchorEquivalence` (PRs #857--#858):
  for an existing bounded genuine leaf preembedding, ONE
  preserved positive E2 witness at each source 1-split and
  ONE preserved positive E3 ordered leaf pair at each source
  2-split are necessary and sufficient for a completely
  induced, all-numerical-meet preserving diary embedding.
  `DiaryFiniteAnchoredFlipCoverCriterion` (#859) quantifies
  this equivalence over every actual target flip.
- `DiaryFiniteAnchorTableCover` (#860) proves an exact
  multivalued FINITE positive-anchor table-cover criterion.
  Candidate source-flip codes are canonical; the original
  target quantifier included redundant RAW Boolean codes.
  `DiaryFiniteCanonicalTargetAnchorCover` (#868) removes
  those duplicates: it suffices to check every genuine
  CANONICAL target flip exactly once.
- `DiaryFinitePairMeetCoupledOneSplit` (#861) verifies V3
  coupling of right-hand E2 incidences across distinct
  one-splits. `DiaryFiniteGlobalDevlinOrientation` (#862)
  proves every finite flip preserves or globally reverses
  ALL marker-one leaf-pair orientation bits with ONE sign.
  `DiaryFiniteGlobalE2ColumnRigidity` (#863) upgrades
  preservation of that sign to the COMPLETE E2 one-split
  columns. A reversed sign is NOT pointwise complementation
  outside a split's predecessor-type cone.
- `DiaryFiniteE3SplitWitnessRigidity` (#864) proves one
  bit of a genuine source S2 witness pair determines an
  ENTIRE E3 two-split column between two flips.
  `DiaryFiniteFaithfulFlipSignature` (#865) combines these:
  one global Devlin marker-one reference bit and one S2
  witness bit per source 2-split uniquely determine the
  complete finite genuine flip, including all E1--E5
  edges and nonedges.
- `DiaryFiniteFixedFlipSignature` (#866) selects the S2
  witnesses ONCE from the source, independently of every
  target flip, and injects the genuine CANONICAL source
  flip orbit into its fixed Boolean signature space.
  `DiaryFiniteUnconditionalFlipOrbitBound` (#867) handles
  zero/one-leaf sources separately (the flip is unique)
  and proves the uniform cardinal bound
  `#Flip(A) <= 2^(1 + number of genuine 2-splits of A)`.
  Applied to B, PR #868 therefore limits the number of
  distinct canonical target cases in the exact anchor
  covering test to `2^(1+t_B)`. Only REALISABLE signatures
  count; no Boolean independence or efficient algorithm
  for listing them is asserted.

### Verified unconditional strong finite flip absorption (29 October 2026)

Merged [PR #952](https://github.com/janhubicka/lean-3-uniform-diaries/pull/952)
(commit `7786736705bd6d09ff36e5449fc826f4a67ed51d`) exports:

- `DiaryLeafPriority.exists_finiteDiary_strong_both_flip_directions`:
  for every `FiniteRoleDiaryBlock A n` there is one finite full
  diary B carrying bounded induced, all-numerical-meet embeddings
  of **every genuine source flip**, and satisfying
  `AbsorbsEveryTargetFlipInside A B n k`: **every genuine
  target flip** contains the fixed UNFLIPPED source A.
- `DiaryLeafPriority.exists_finiteDiary_universal_flip_absorber`:
  the strong second assertion as a standalone unconditional theorem.
- `canonicalCausalOrbitFiniteTarget_firstS2CrossMeet`: the exact
  cross-copy two-split meet persists through dummy-tail extension,
  one-pass full completion and finite leaf-meet support.

The true constrained source flip orbit has one GLOBAL Devlin sign
and one source-fixed genuine S2 witness bit per two-split. Distinct
signs remain distinct in every target flip. At the FIRST differing
true S2 bit with equal signs, the corresponding two source leaf
pairs have a full meet at their shared image of the source split.
Every target flip must still give opposite E3 incidences there.
Hence the feedback on explicit canonical branch maps is injective,
and thus surjective on the finite realisable orbit; the baseline
source has a preimage in every target flip. This uses neither
independent free Boolean coordinates nor arbitrary chosen maps.

Exact integrated CI: **9886 Lean build jobs**; **747 local Lean files**
without `sorry`, `admit` or local axioms/constants; **2224 theorem
endpoints** with only `Classical.choice`, `Quot.sound` and `propext`;
both finite regressions green (**44592** auxiliary configurations
and **118324** exact-meet embeddings, including **21318** respecting).

### Verified finite-source generic leaf unavoidability (30 October 2026)

Merged [PR #953](https://github.com/janhubicka/lean-3-uniform-diaries/pull/953)
and [PR #954](https://github.com/janhubicka/lean-3-uniform-diaries/pull/954)
(commit `e32afbb3950bcb2066f87aff0fb1fd724acb3120`) complete the
FINITELY GENERATED lower-bound application. Given ANY finite full
diary A, countable full RoleDiary K, and any unordered induced
embedding F of the enumerated generic hypergraph into K whose
image consists of genuine leaves, there is a strictly increasing
marker-fixing induced copy g of the ENTIRE finite diary A in K,
with all source leaf images inside F[G], preserving exact singleton
and full ordered-pair meets of source leaves. There is NO
assumption that F was order-preserving, and edges AND nonedges
of source triples involving splits are also induced.

This uses the genuine countable positive-cut four-tail
preembedding H→K, the verified single finite B→H completion,
the exact induced finite leaf-meet support flip of B inside K,
and the unrestricted finite target-flip absorption #952.
No global preservation of arbitrary MIXED ambient meets is
claimed for the countable composition. PR #954 passed an
exact-head full build (9888 jobs), a 749-file no-admissions check,
2230 theorem endpoints with only the expected kernel axioms,
and both finite regressions (44592 auxiliary configurations;
118324 exact-meet embeddings).

**Still open:** the manuscript's printed
`thm:unavoidable` quantifies over an ARBITRARY COUNTABLE source
diary, not just a finite one. Independent finite copies do not
automatically yield one coherent countable embedding. PR #955
introduces cofinal nested finite leaf-meet supports and PR #956
is a conditional compatible-stage gluing interface; neither
constructs the needed relatively extending stage embeddings.
The manuscript upper-bound proof also needs a separate repair
of its circular invocation of the final strong Ramsey theorem.
The frozen circulation `main.tex` is unchanged; the manuscript
repository's standalone sign-rooted notes contain the finite
proof and adversarial audit.

### Verified finite diary embedding in a generic leaf range (30 October 2026)

PR #959, merged as `5cd858269bbcc78d8d774e42d9e0d4ac0d77cdb0`, exports
`FiniteLeafPreembedding.toMeetEmbedding_into_countable` and
`exists_finiteDiary_full_embedding_in_generic_leaf_range`.
The E-only marker dichotomy for mixed singleton and auxiliary meets
now holds in countable full target diaries, so an induced finite
leaf preembedding is a genuine full finite meet embedding.

For every finite full source diary A, every prescribed unordered
generic-to-leaf embedding into a countable full diary K contains
an induced full meet-preserving copy of A, with all A leaves in
the ORIGINAL generic image. Exact-head CI passed 9889 jobs,
750 local sources without admissions, 2238 axiom endpoints (only
the three expected kernel axioms), and both exhaustive regressions.

This proves finite-source diary unavoidability only; the infinite
source version still requires coherent gluing of finite embeddings.

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
