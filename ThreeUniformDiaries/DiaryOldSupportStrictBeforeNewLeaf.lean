import ThreeUniformDiaries.DiaryCountableCofinalFiniteSupports

/-!
# Track A: old canonical leaf-meet supports lie STRICTLY before the next true leaf

At a source cutoff m >= 3, the supported source vertices S_m
consist exactly of the markers 0,1,2, genuine selected source
leaves a<m, their capped singleton meets and full ordered-pair
meets. Both meets are numerically at or below a selected leaf.
Hence EVERY u in S_m satisfies u<m, including split generators
which are not source leaves. This does NOT require the full
RoleDiary axioms, only the literal canonical support definition
and exact generic numerical meet upper bounds.

In particular, when m is the next TRUE source leaf, m is NOT
already in its old supported source S_m; indeed max(S_m)<m.

This explicitly explains the limit of the CI-green bounded-gap
and complete-initial-prefix compactness theorems: all source
positions protected between old supported endpoints lie below
m, so stabilizing all such intervals does NOT stabilize the
new rightmost leaf image at source m.

No eventual new-image boundedness, relative extension, countable
diary unavoidability or strong diary upper-bound claim is made.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For ANY ordered ternary graph H, at every numerical source
cutoff m>=3 ALL vertices of the canonical OLD selected-leaf and
numerical S1/S2 generator support lie strictly below m.

This uses the actual selected leaf prefix L_m and the numeric
oneMeet/twoMeet upper bounds, not a RoleDiary assumption. -/
theorem countableDiaryFiniteSupport_lt_cut
    (H : Ordered3Graph Nat) (m u : Nat)
    (hm : 3 ≤ m)
    (hu : u ∈ countableDiaryFiniteSupport H m) :
    u < m := by
  classical
  let L : Finset Nat := countableDiaryLeafPrefix H m
  have hLeafLt (a : Nat) (ha : a ∈ L) : a < m :=
    ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.1
  change u ∈ (Finset.range 3 ∪ L) ∪
    (finiteOneMeetSupport H L ∪ finiteTwoMeetSupport H L) at hu
  rcases Finset.mem_union.mp hu with hFront | hMeets
  · rcases Finset.mem_union.mp hFront with hMarker | hLeaf
    · have hu3 : u < 3 := Finset.mem_range.mp hMarker
      omega
    · exact hLeafLt u hLeaf
  · rcases Finset.mem_union.mp hMeets with hOne | hTwo
    · change u ∈ ((L.product L).filter
        (fun p : Nat × Nat => p.1 ≠ p.2)).image
          (fun p : Nat × Nat => H.oneMeetLevel p.1 p.2) at hOne
      obtain ⟨⟨a,b⟩,hp,hEq⟩ := Finset.mem_image.mp hOne
      obtain ⟨hpProd,_hNe⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha,_hb⟩ := Finset.mem_product.mp hpProd
      rw [← hEq]
      have hBound : H.oneMeetLevel a b ≤ a :=
        (H.oneMeetLevel_le_min a b).trans (min_le_left a b)
      exact lt_of_le_of_lt hBound (hLeafLt a ha)
    · change u ∈
        ((finiteOrderedLeafPairs L).product
          (finiteOrderedLeafPairs L)).image
          (fun p : (Nat × Nat) × (Nat × Nat) =>
            H.twoMeetLevel p.1.1 p.1.2 p.2.1 p.2.2) at hTwo
      obtain ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,hp,hEq⟩ :=
        Finset.mem_image.mp hTwo
      obtain ⟨hpAB,_hpCD⟩ := Finset.mem_product.mp hp
      obtain ⟨hpABProd,_hab⟩ := Finset.mem_filter.mp hpAB
      obtain ⟨ha,_hb⟩ := Finset.mem_product.mp hpABProd
      rw [← hEq]
      have hBound : H.twoMeetLevel a b c d ≤ a :=
        (H.twoMeetLevel_le_min a b c d).trans
          (min_le_left _ _)
      exact lt_of_le_of_lt hBound (hLeafLt a ha)

/-- In particular the NUMERICAL maximum of the whole actual
old canonical support is strictly below the new source cutoff
m>=3, not merely its last selected true leaf. -/
theorem countableDiaryFiniteSupport_sup_lt_cut
    (H : Ordered3Graph Nat) (m : Nat) (hm : 3 ≤ m) :
    (countableDiaryFiniteSupport H m).sup id < m := by
  have hBound :
      (countableDiaryFiniteSupport H m).sup id ≤ m - 1 := by
    apply Finset.sup_le
    intro u hu
    have hLt := countableDiaryFiniteSupport_lt_cut H m u hm hu
    change u ≤ m - 1
    omega
  omega

/-- The genuinely next source LEAF m never belongs to its own
old supported canonical finite meet record S_m; its coordinate
is NOT captured by any old bounded-prefix stabilization. -/
theorem next_true_leaf_not_in_old_finite_support
    {H : Ordered3Graph Nat} {m : Nat}
    (hm : IsLeaf H m) :
    m ∉ countableDiaryFiniteSupport H m := by
  intro h
  exact (Nat.lt_irrefl m)
    (countableDiaryFiniteSupport_lt_cut H m m hm.1 h)

end DiaryLeafPriority
end ThreeUniformDiaries
