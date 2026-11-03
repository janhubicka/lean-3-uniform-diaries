import ThreeUniformDiaries.DiaryExistenceFiniteEnumNode

/-!
# Track B: finite diary leaves are order-isomorphic to the original EnumNode

The finite Eq-on-edges theorem produces an increasing Fin n -> Fin m
map and shows its image is all genuinely marked leaves of the bounded
finite diary. Package that map as an equivalence with the actual
leaf subtype and prove that it preserves and reflects order and
all genuine increasing 3-edges.

This is the literal mathematical meaning of "the ordered leaf reduct
is isomorphic to H". It does not reinterpret the zero-extended
Nat carrier of a finite diary as a globally infinite RoleDiary.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every intrinsic finite ordered 3-graph admits a finite RoleDiary
whose genuine ordered leaves are *equivalent* to the original finite
vertices, with order and induced edge/nonedge equivalences. -/
theorem exists_finite_diary_order_equiv_leaf_reduct
    (n : Nat) (A : EnumNode n) :
    ∃ (F : Ordered3Graph Nat) (m : Nat)
        (e : Fin n ≃ {v : Fin m // IsLeaf F v.val}),
      FiniteRoleDiaryBlock F m ∧
      (∀ i j : Fin n,
        (i < j ↔ (e i).val < (e j).val)) ∧
      (∀ i j k : Fin n, i < j → j < k →
        (F.edge (e i).val.val (e j).val.val (e k).val.val ↔
          A.triple i.val j.val k.val = true)) := by
  classical
  obtain ⟨F, m, f, hDiary, hMono, hLeaf, hOnto, hEdge⟩ :=
    exists_finite_diary_exact_EnumNode_leaf_reduct n A
  let lift : Fin n → {v : Fin m // IsLeaf F v.val} :=
    fun i => ⟨f i, hLeaf i⟩
  have hfMono : StrictMono f := fun i j hij => hMono i j hij
  have hInj : Function.Injective lift := by
    intro i j hij
    apply hfMono.injective
    exact congrArg Subtype.val hij
  have hSurj : Function.Surjective lift := by
    intro v
    obtain ⟨i, hi⟩ := hOnto v.val v.property
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hi
  let e : Fin n ≃ {v : Fin m // IsLeaf F v.val} :=
    Equiv.ofBijective lift ⟨hInj, hSurj⟩
  have hEval : ∀ i : Fin n, (e i).val = f i := by
    intro i
    rfl
  refine ⟨F, m, e, hDiary, ?_, ?_⟩
  · intro i j
    constructor
    · intro hij
      rw [hEval i, hEval j]
      exact hMono i j hij
    · intro hij
      by_contra hNot
      have hji : j ≤ i := le_of_not_gt hNot
      rcases eq_or_lt_of_le hji with heq | hjlt
      · subst j
        exact (lt_irrefl _ hij)
      · have hReverse : (e j).val < (e i).val := by
          rw [hEval j, hEval i]
          exact hMono j i hjlt
        exact (lt_asymm hij hReverse)
  · intro i j k hij hjk
    change F.edge (f i).val (f j).val (f k).val ↔
      A.triple i.val j.val k.val = true
    exact hEdge i j k hij hjk

end DiaryLeafPriority
end ThreeUniformDiaries
