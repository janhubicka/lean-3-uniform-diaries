import ThreeUniformDiaries.DiaryFinitePositiveAnchorEquivalence
import ThreeUniformDiaries.DiaryFiniteBoundedUniversality

/-!
# Exact geometric reformulation of the second finite diary flip property

The original every-target-flip absorption predicate demands full
induced, all-mixed-meet preserving copies of A in every genuine
flip T of B. For an arbitrary finite source diary A, the
positive-anchor equivalence gives the following exact reduction:

For EVERY genuine target flip T, find SOME bounded finite
leaf preembedding of A into T (preserving roles, the induced
leaf-only hypergraph, and all exact singleton/pair meets of
source leaves), whose images preserve just ONE positive E2
anchor per source 1-split and ONE positive E3 anchor per
source 2-split.

All remaining split-containing edge/nonedge incidences,
both Devlin marker bits and ALL mixed numerical meets then
follow automatically. Conversely, a fully protected embedded
copy supplies such a leaf preembedding and source anchors.

The quantifiers are existential separately for each target
flip; one fixed family of selected maps, global feedback
injectivity and a free Boolean cube are NOT required.
This is an equivalence, not a construction of an absorber.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For a fixed finite source A and target B, strong absorption
under every genuine target flip is exactly the problem of
finding a correctly anchored bounded LEAF preembedding for
each target flip. The anchors may be chosen separately in
each flip. -/
theorem absorbsEveryTargetFlipInside_iff_anchored_leaf_copies
    {A B : Ordered3Graph Nat} {n k : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    AbsorbsEveryTargetFlipInside A B n k ↔
      ∀ T : Ordered3Graph Nat,
        FiniteDiaryFlip B T k →
        ∃ (f : Nat → Nat),
          ∃ Q : FiniteLeafPreembedding A T n k f,
            (∀ s : Nat, IsOneSplit A s →
              ∃ a : Nat, IsLeaf A a ∧ s < a ∧ a < n ∧
                A.edge 0 s a ∧ T.edge 0 (f s) (f a)) ∧
            (∀ s : Nat, IsTwoSplit A s →
              ∃ a b : Nat, a < b ∧ b < n ∧
                IsLeaf A a ∧ IsLeaf A b ∧ s < a ∧
                A.edge s a b ∧ T.edge (f s) (f a) (f b)) := by
  constructor
  · intro hAbs T FT
    obtain ⟨f,E⟩ := hAbs T FT
    have Q : FiniteLeafPreembedding A T n k f :=
      E.leafPreembedding_after_target_flip
        (FiniteDiaryFlip.refl FT.target_diary)
    have hAnchors :=
      (finite_leafPreembedding_boundedEmbedding_iff_positive_anchors
        DA FT.target_diary Q).mp E
    exact ⟨f,Q,hAnchors⟩
  · intro hCover T FT
    obtain ⟨f,Q,hOne,hTwo⟩ := hCover T FT
    exact ⟨f,
      (finite_leafPreembedding_boundedEmbedding_iff_positive_anchors
        DA FT.target_diary Q).mpr ⟨hOne,hTwo⟩⟩

end DiaryLeafPriority
end ThreeUniformDiaries
