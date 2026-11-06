import ThreeUniformDiaries.DiarySumOverAllIncreasingPresentations

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open _root_.ThreeUniformDiaries.Ordered3Graph

theorem isFiniteFullDiaryOfUnordered_congr_of_permutation
    {a : Nat} (A B : EnumNode a)
    (τ : Equiv.Perm (Fin a))
    (hIso : ∀ i j k : Fin a,
      A.toOrdered3Graph.unorderedEdge i.val j.val k.val ↔
        B.toOrdered3Graph.unorderedEdge
          (τ i).val (τ j).val (τ k).val)
    (S : ProtectedSource 0) :
    IsFiniteFullDiaryOfUnordered A S ↔
      IsFiniteFullDiaryOfUnordered B S := by
  classical
  constructor
  · rintro ⟨hFull, hCard, σ, hEdges⟩
    let ρ : Equiv.Perm (Fin a) := τ.symm.trans σ
    refine ⟨hFull, hCard, ρ, ?_⟩
    intro i j k
    have hBack :
        B.toOrdered3Graph.unorderedEdge i.val j.val k.val ↔
          A.toOrdered3Graph.unorderedEdge
            (τ.symm i).val (τ.symm j).val (τ.symm k).val := by
      simpa using (hIso (τ.symm i) (τ.symm j) (τ.symm k)).symm
    simpa only [ρ, Equiv.trans_apply] using
      (hBack.trans (hEdges (τ.symm i) (τ.symm j) (τ.symm k)))
  · rintro ⟨hFull, hCard, σ, hEdges⟩
    let ρ : Equiv.Perm (Fin a) := τ.trans σ
    refine ⟨hFull, hCard, ρ, ?_⟩
    intro i j k
    simpa only [ρ, Equiv.trans_apply] using
      ((hIso i j k).trans (hEdges (τ i) (τ j) (τ k)))

theorem allGenuineUnmarkedDiarySources_eq_of_unorderedIso
    {a : Nat} (A B : EnumNode a)
    (τ : Equiv.Perm (Fin a))
    (hIso : ∀ i j k : Fin a,
      A.toOrdered3Graph.unorderedEdge i.val j.val k.val ↔
        B.toOrdered3Graph.unorderedEdge
          (τ i).val (τ j).val (τ k).val) :
    allGenuineUnmarkedDiarySources A =
      allGenuineUnmarkedDiarySources B := by
  classical
  ext S
  rw [mem_allGenuineUnmarkedDiarySources_iff_fullDiaryOfUnordered,
      mem_allGenuineUnmarkedDiarySources_iff_fullDiaryOfUnordered]
  exact isFiniteFullDiaryOfUnordered_congr_of_permutation A B τ hIso S

theorem allIncreasingPresentations_diarySum_eq_of_unorderedIso
    {a : Nat} (A B : EnumNode a)
    (τ : Equiv.Perm (Fin a))
    (hIso : ∀ i j k : Fin a,
      A.toOrdered3Graph.unorderedEdge i.val j.val k.val ↔
        B.toOrdered3Graph.unorderedEdge
          (τ i).val (τ j).val (τ k).val) :
    (∑ P ∈ allIncreasingPresentations A,
       (unmarkedDiariesOfIncreasingPresentation A P).card) =
      (∑ P ∈ allIncreasingPresentations B,
       (unmarkedDiariesOfIncreasingPresentation B P).card) := by
  calc
    (∑ P ∈ allIncreasingPresentations A,
        (unmarkedDiariesOfIncreasingPresentation A P).card) =
      (allGenuineUnmarkedDiarySources A).card :=
      (unmarkedDiaryCount_eq_sum_allIncreasingPresentations A).symm
    _ = (allGenuineUnmarkedDiarySources B).card := by
      rw [allGenuineUnmarkedDiarySources_eq_of_unorderedIso A B τ hIso]
    _ = (∑ P ∈ allIncreasingPresentations B,
        (unmarkedDiariesOfIncreasingPresentation B P).card) :=
      unmarkedDiaryCount_eq_sum_allIncreasingPresentations B

end ATRFiniteDecoder
end ThreeUniformDiaries
