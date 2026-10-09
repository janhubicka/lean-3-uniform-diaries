# lean-3-uniform-diaries

Lean formalisation accompanying the 3-uniform diaries manuscript. The
complete auxiliary type-respecting Ramsey theorem has **not** yet been
formalised, although the root-based generic branch embedding is now checked.

## Verified components

All imported proof modules build in CI; the exported results below are
covered by the axiom audit in scripts/CheckAxioms.lean.

- Auxiliary/ordinary type representations and their decomposition,
  successor identities and selected-cut agreement (AuxTypes, TypeTrees,
  TypeRepresentation, CanonicalAgreement).
- Abstract canonical maps and their composition (CanonicalMap).
- Induced branch codes in K_I, including tests against every indexed
  relative K_I node, not just those on the branch (BranchHypergraph,
  RelativeBranchHypergraph, BranchTypeAgreement, BranchCutBoundary).
- Size-first enumeration of K_I and source branch predecessor schedule
  (SizeFirstEnumeration, SizeFirstSourceTests, SizeFirstParentSchedule).
- Generic induced embedding recursions with predecessor-relative C1/C2,
  both root-based and fixing a prescribed nonempty initial segment
  (InheritedGapExtension, CountableInheritedEmbedding,
  FixedPrefixCountableEmbedding, FixedPrefixGapStep).
- **Root-based canonical branch aux-type respect:** RootBranchAuxEmbedding
  combines indexed source type tests with globally omitted target
  gap propagation. The global K_I embedding itself need not preserve
  all aux types.
- **Exact singleton and auxiliary meet levels:** ExactMeetsFromTypes
  derives literal capped meet equations from cutwise type agreement.
  RootBranchExactMeets verifies both equations on actual root-based
  canonical branches.
- Conditional final Ramsey transfer through K_I and a checked
  finite-colour Milliken consequence (AuxRamseyTransfer,
  MillikenFiniteColour).

## Remaining obligations

1. **Fixed-prefix K_I branch transfer (n > 0).** Combine the actual
   indexed K_I initial segment and predecessor schedule with the
   fixed-prefix inherited recursion. Then verify omitted target tests
   and both exact meets on all canonical branches. Work toward this
   is in PRs #31 and #32. Lemma Kiemb remains partial.
2. **Finite strong-tree coding and composition.** Check the three
   meet-closed coordinate sets, their strong vector subtree
   completion, concrete canonical maps and composition (including
   manuscript Lemmas Aemb, auxtypeemb and canonicalcomposition).
3. **Unconditional Ramsey theorem.** Instantiate the abstract
   AuxRamseyTransfer coding identities with these constructions.

## Adversarial C2 check

GapCounterexample records a finite diagram refuting the earlier
zero-on-all-omitted-pairs induction. The predecessor-relative
inheritance repair copies omitted pairs below their parent and zeros
them at or above the parent. It has now been validated through the
**root-based** exact-meet equations; it is not yet a proof of the full
fixed-prefix lemma or of the Ramsey theorem.
