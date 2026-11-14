import ThreeUniformDiaries.DiaryGoodColourOnePointGenericCopy

/-!
# Track A: a UNIVERSAL vertex colour has all finite generic one-point extensions

English-first adversarial audit: 3-uniform-diaries PR #363.

If every vertex of an enumerated generic 3-hypergraph satisfies a
predicate C, the general colour-relative one-point extension schema
holds at EVERY finite induced increasing source stage s. The genuine
generic extension proof FiniteGenericStage.newVertex_spec produces
a next vertex v ≥ s.bound realizing ALL next-source E5 edge AND
nonedge tests, and the global assumption gives C(v).

The pending first-source-leaf specialization will show that the
COMPLETE oldStageTailCut singleton colour of every genuine target
leaf in the ORIGINAL unordered F[G] range is literally constant.
Therefore the strong sufficient colour-extension condition is
UNCONDITIONALLY satisfied at that first leaf for ALL n, not just
the n=0,1 cases of the earlier chosen-good-colour theorem.

For later source leaves, old-supported maps and E2/E3/E5 data
make the full mixed old-cut colour nonconstant in general.
No countable diary unavoidability or persistent successor follows.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- If C literally holds on ALL vertices of an enumerated
generic 3-graph, its colour-relative finite-stage extension
property holds for EVERY actual induced increasing stage of
arbitrary finite size, including all nontrivial new E5 tests.

This is a direct use of the already verified generic finite
extension theorem, not an application of Ramsey or a compactness
principle. -/
theorem GenericEnumerated3Graph.has_generic_colour_onePointExtensions_of_all
    (G : GenericEnumerated3Graph)
    (C : Nat → Prop) (hAll : ∀ t : Nat, C t) :
    HasGenericColourOnePointExtensions G C := by
  intro n s _hOld
  have hSpec := s.newVertex_spec
  refine ⟨s.newVertex, hSpec.1, hAll s.newVertex, ?_⟩
  intro i j hij
  exact hSpec.2 i j hij

end DiaryLeafPriority
end ThreeUniformDiaries
