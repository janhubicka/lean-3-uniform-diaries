import ThreeUniformDiaries.DiaryExistenceUnconditional

/-!
# Track B: the countable full diary has EXACTLY the original leaf order

The verified complete countable-diary construction gives a strictly
increasing induced embedding of an arbitrary ordered 3-graph H on Nat
into a full RoleDiary D, and proves that the image contains every
genuine leaf of D. Package the map as a true equivalence with the
subtype of all leaves, reflecting order and all actual hyperedges and
nonedges on increasing triples.

This theorem is not an appeal to the false universal old-cut
prediary completion lemma. It uses only the already-verified exact
leaf census and induced source embedding.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every countably infinite enumerated ordered 3-hypergraph is
literally order-isomorphic, including induced edges/nonedges, to the
*entire* genuine leaf reduct of a full countable RoleDiary. -/
theorem exists_countable_diary_order_equiv_leaf_reduct
    (H : Ordered3Graph Nat) :
    ∃ (D : Ordered3Graph Nat)
        (f : Nat ≃ {v : Nat // IsLeaf D v}),
      RoleDiary D ∧
      (∀ a b : Nat, a < b ↔ (f a).val < (f b).val) ∧
      (∀ a b c : Nat, a < b → b < c →
        (D.edge (f a).val (f b).val (f c).val ↔
          H.edge a b c)) := by
  classical
  obtain ⟨D, hDiary, e, hLeaf, hOnto⟩ :=
    exists_countable_full_diary_with_exact_leaf_reduct H
  let lift : Nat → {v : Nat // IsLeaf D v} :=
    fun u => ⟨e u, hLeaf u⟩
  have hInj : Function.Injective lift := by
    intro a b hab
    apply e.strictMono.injective
    exact congrArg Subtype.val hab
  have hSurj : Function.Surjective lift := by
    intro v
    obtain ⟨u, hu⟩ := hOnto v.val v.property
    refine ⟨u, ?_⟩
    apply Subtype.ext
    exact hu
  let f : Nat ≃ {v : Nat // IsLeaf D v} :=
    Equiv.ofBijective lift ⟨hInj, hSurj⟩
  have hEval : ∀ u : Nat, (f u).val = e u := by
    intro u
    rfl
  refine ⟨D, f, hDiary, ?_, ?_⟩
  · intro a b
    constructor
    · intro hab
      rw [hEval a, hEval b]
      exact e.strictMono hab
    · intro hab
      by_contra hNot
      have hba : b ≤ a := le_of_not_gt hNot
      rcases eq_or_lt_of_le hba with heq | hlt
      · subst b
        exact (lt_irrefl _ hab)
      · have hRev : (f b).val < (f a).val := by
          rw [hEval b, hEval a]
          exact e.strictMono hlt
        exact (lt_asymm hab hRev)
  · intro a b c hab hbc
    change D.edge (e a) (e b) (e c) ↔ H.edge a b c
    exact (e.edge_iff hab hbc).symm

end DiaryLeafPriority
end ThreeUniformDiaries
