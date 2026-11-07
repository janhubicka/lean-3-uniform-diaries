import ThreeUniformDiaries.DiaryTailSingletonTypeCone
import ThreeUniformDiaries.DiaryOneNewLeafSupportSuccessor

/-!
# The newly selected leaf is the largest source support coordinate

At a genuine source leaf m, the exact canonical support S_(m+1)
consists of 0,1,2, genuine selected leaves at most m, singleton
meets capped by selected leaves, and full ordered-pair meets
capped by selected first coordinates.

Thus every source coordinate in S_(m+1) is <=m. This simple
structural fact is needed to replace only the new largest leaf
while preserving all older supported source coordinates, without
inventing role or meet assumptions.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every supported generator at the successor of a genuine
leaf is at most that new leaf in the source enumeration. -/
theorem countableDiaryFiniteSupport_succ_le_new_leaf
    (H : Ordered3Graph Nat) (m u : Nat) (hm : IsLeaf H m)
    (hu : u ∈ countableDiaryFiniteSupport H (m + 1)) :
    u ≤ m := by
  classical
  let L := countableDiaryLeafPrefix H (m + 1)
  have hSelected (a : Nat) (ha : a ∈ L) : a ≤ m := by
    have hCut :=
      ((mem_countableDiaryLeafPrefix_iff H (m + 1) a).mp ha).2.1
    omega
  change u ∈ finiteLeafMeetSupport H L at hu
  change u ∈ (Finset.range 3 ∪ L) ∪
    (finiteOneMeetSupport H L ∪ finiteTwoMeetSupport H L) at hu
  rcases Finset.mem_union.mp hu with hFront | hMeets
  · rcases Finset.mem_union.mp hFront with hMarker | hLeaf
    · have huSmall := Finset.mem_range.mp hMarker
      have hm3 := hm.1
      omega
    · exact hSelected u hLeaf
  · rcases Finset.mem_union.mp hMeets with hOne | hTwo
    · change u ∈ ((L.product L).filter
          (fun p : Nat × Nat => p.1 ≠ p.2)).image
          (fun p : Nat × Nat => H.oneMeetLevel p.1 p.2) at hOne
      obtain ⟨⟨a,b⟩,hp,hEq⟩ := Finset.mem_image.mp hOne
      obtain ⟨hp,_hab⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha,_hb⟩ := Finset.mem_product.mp hp
      have hCap : H.oneMeetLevel a b ≤ a :=
        (H.oneMeetLevel_le_min a b).trans (min_le_left _ _)
      have haM := hSelected a ha
      calc
        u = H.oneMeetLevel a b := hEq.symm
        _ ≤ a := hCap
        _ ≤ m := haM
    · change u ∈
        ((finiteOrderedLeafPairs L).product
          (finiteOrderedLeafPairs L)).image
          (fun p : (Nat × Nat) × (Nat × Nat) =>
            H.twoMeetLevel p.1.1 p.1.2 p.2.1 p.2.2) at hTwo
      obtain ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,hp,hEq⟩ :=
        Finset.mem_image.mp hTwo
      obtain ⟨habP,_hcdP⟩ := Finset.mem_product.mp hp
      obtain ⟨habP,_hab⟩ := Finset.mem_filter.mp habP
      obtain ⟨ha,_hb⟩ := Finset.mem_product.mp habP
      have hCap : H.twoMeetLevel a b c d ≤ a :=
        (H.twoMeetLevel_le_min a b c d).trans (min_le_left _ _)
      have haM := hSelected a ha
      calc
        u = H.twoMeetLevel a b c d := hEq.symm
        _ ≤ a := hCap
        _ ≤ m := haM

end DiaryLeafPriority
end ThreeUniformDiaries
