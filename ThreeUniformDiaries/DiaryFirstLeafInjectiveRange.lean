import ThreeUniformDiaries.DiaryFirstLeafReservedSuccessor

/-!
# An injective prescribed leaf embedding supplies a high first leaf

The positive first-leaf relative extension from the previous module
requires a target leaf v >= the source leaf index m. In the actual
unavoidability setup the prescribed map F : Nat -> Nat is an embedding,
hence injective, and its range consists of target leaves.

An injective map Nat -> Nat has unbounded numerical image. Thus the
first new source leaf stage always has a reserved successor for
any injective F whose whole range consists of target leaves.

This is not a general leaf-step realization result: from the second
source leaf onwards the new S1/S2 generators and mixed incidences
become nontrivial.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A total injection from the infinite natural numbers cannot
have range bounded by a natural number. This elementary statement
does not use diary structure or a genericity hypothesis. -/
theorem exists_ge_of_injective_nat
    (F : Nat → Nat) (hF : Function.Injective F) (n : Nat) :
    ∃ t : Nat, n ≤ F t := by
  classical
  by_contra hNo
  have hBound (t : Nat) : F t < n := by
    by_contra hNot
    exact hNo ⟨t, by omega⟩
  let f' : Nat → Fin n := fun t => ⟨F t, hBound t⟩
  have hInj : Function.Injective f' := by
    intro x y hEq
    apply hF
    exact congrArg Fin.val hEq
  exact Finite.false (Finite.of_injective f' hInj)

/-- The first selected source leaf can always be placed at a
sufficiently high member of an arbitrary injective prescribed
target-leaf range. The returned finite-stage embedding is
admissible, future-order-reserved, and trivially preserves any
earlier selected source leaves, since there are none. -/
theorem exists_reserved_successor_of_first_leaf_injective_range
    {H K : Ordered3Graph Nat}
    {F f : Nat → Nat} {m : Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (hm : IsLeaf H m)
    (hEmpty : countableDiaryLeafPrefix H m = ∅)
    (hFinj : Function.Injective F)
    (hFleaf : ∀ t : Nat, IsLeaf K (F t)) :
    ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1) g ∧
      (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
        g u = f u) := by
  obtain ⟨t, hHigh⟩ := exists_ge_of_injective_nat F hFinj m
  exact exists_reserved_successor_of_first_leaf
    DH DK hm hEmpty (hFleaf t) hHigh

end DiaryLeafPriority
end ThreeUniformDiaries
