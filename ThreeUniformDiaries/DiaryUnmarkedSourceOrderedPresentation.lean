import ThreeUniformDiaries.DiaryOrderedLeafEnumPresentation
import ThreeUniformDiaries.DiaryOrderedLeafPresentationSignatures

/-!
# Track C: every genuine UNMARKED diary source presents unordered A

The verified finite counting family consists of deduplicated unmarked
finite full diary sources whose genuine leaves induce the unordered A.
An arbitrary source in that family has some exhaustive A-marking,
but its counted identity does not contain that marking as data.

By the verified membership characterisation, one such marking
exists. The canonical increasing leaf enumeration from Track C
then produces a genuine ordered finite EnumNode of size |A|, and
its literal edge table is A with a concrete permutation of labels.

Thus the finite source-counting family is precisely a family
of finite diaries whose increasing leaf reduct is SOME ordered
presentation of the fixed underlying unordered A. No marking is
left as an extra hypothesis of the resulting theorem.

This does not assert that every conceivable increasing presentation
has a full diary, or prove the separate countable lower bound.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- Actual unmarked-source formulation of the finite ordered-leaf
presentation theorem. Membership in the deduplicated family is
the ONLY assumption, and gives the marking witness automatically. -/
theorem allGenuineUnmarkedDiarySources_has_increasingPresentation
    {a : Nat} (A : EnumNode a)
    (S : ProtectedSource 0)
    (hS : S ∈ allGenuineUnmarkedDiarySources A) :
    ∃ (hCard : S.leafPositions.card = a)
      (σ : Equiv.Perm (Fin a)),
      ∀ (i j k : Fin a), i < j → j < k →
      (S.increasingLeafEnum a hCard).toOrdered3Graph.edge
        i.val j.val k.val ↔
      A.toOrdered3Graph.unorderedEdge
        (σ.symm i).val (σ.symm j).val (σ.symm k).val := by
  classical
  let p : GenuineDiaryMarkingFibre A S :=
    Classical.choice
      ((mem_allGenuineUnmarkedDiarySources_iff A S).mp hS)
  let T : MarkedFiniteSource 0 a := ⟨S, p.val⟩
  have hShape : IsGenuineMarkedDiaryShape A T := p.property
  let hCard : S.leafPositions.card = a :=
    genuineMarkedDiaryShape_leafPositions_card A T hShape
  let σ : Equiv.Perm (Fin a) :=
    genuineMarkedDiaryShape_labelRankPerm A T hShape
  refine ⟨hCard, σ, ?_⟩
  intro i j k hij hjk
  exact genuineMarkedDiaryShape_increasingLeafEnum_presentation
    A T hShape i j k hij hjk

/-- In particular every counted unmarked diary source for A
has EXACTLY a genuine source leaves; this is not an additional
size assumption imposed on its finite source diagram. -/
theorem allGenuineUnmarkedDiarySources_leaf_card
    {a : Nat} (A : EnumNode a)
    (S : ProtectedSource 0)
    (hS : S ∈ allGenuineUnmarkedDiarySources A) :
    S.leafPositions.card = a := by
  obtain ⟨hCard, _, _⟩ :=
    allGenuineUnmarkedDiarySources_has_increasingPresentation
      A S hS
  exact hCard

/-- Every REALISED ordered signature in the partition of
the unmarked diary count comes from an actual source whose
finite increasing leaf EnumNode is an ordered presentation
of the given unordered hypergraph A. The witness is obtained
from membership in the verified finite source-counting family,
not supplied as an independent premise. -/
theorem realizedOrderedLeafPresentation_has_A_presentation
    {a : Nat} (A : EnumNode a)
    (P : Finset (Nat × Nat × Nat))
    (hP : P ∈ allRealizedOrderedLeafPresentations A) :
    ∃ S ∈ allGenuineUnmarkedDiarySources A,
      S.orderedLeafEdgeSignature = P ∧
      ∃ (hCard : S.leafPositions.card = a)
        (σ : Equiv.Perm (Fin a)),
        ∀ (i j k : Fin a), i < j → j < k →
        (S.increasingLeafEnum a hCard).toOrdered3Graph.edge
          i.val j.val k.val ↔
        A.toOrdered3Graph.unorderedEdge
          (σ.symm i).val (σ.symm j).val (σ.symm k).val := by
  classical
  change P ∈ (allGenuineUnmarkedDiarySources A).image
      (fun S => S.orderedLeafEdgeSignature) at hP
  obtain ⟨S, hS, hSP⟩ := Finset.mem_image.mp hP
  obtain ⟨hCard, σ, hPresentation⟩ :=
    allGenuineUnmarkedDiarySources_has_increasingPresentation
      A S hS
  exact ⟨S, hS, hSP, hCard, σ, hPresentation⟩

end ATRFiniteDecoder
end ThreeUniformDiaries
