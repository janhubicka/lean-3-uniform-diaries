import ThreeUniformDiaries.DiaryLeafGeneratedStageCompatibility

/-!
# All images of a finite leaf-generated support are numerically bounded

An admissible stage is defined by a total Nat map, but its source
support is a FINITE leaf-meet closure. Its three marker images are
0,1,2; every generated split image is a target singleton/full pair
meet of selected leaf images and therefore cannot exceed those images.

Consequently, for fixed images of finitely many selected leaves,
there is an explicit finite range for ALL images on the stage support.
This is a finite-search reduction, not a realization or compactness
argument, and does not prove any successor exists.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace AdmissibleCofinalDiaryStage

variable {H K : Ordered3Graph Nat} {F : Nat → Nat}
variable {m : Nat} {f : Nat → Nat}

/-- An admissible finite support map is bounded on every supported
source vertex by the maximum of the three marker levels and the
images of its finitely many selected leaves. -/
theorem image_le_support_leaf_sup
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (u : Nat) (hu : u ∈ countableDiaryFiniteSupport H m) :
    f u ≤ max 2 ((countableDiaryLeafPrefix H m).sup f) := by
  classical
  let L := countableDiaryLeafPrefix H m
  have hLLeaf : ∀ a : Nat, a ∈ L → IsLeaf H a := by
    intro a ha
    exact ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.2
  have hInSupport : ∀ a : Nat, a ∈ L →
      a ∈ countableDiaryFiniteSupport H m := by
    intro a ha
    exact mem_finiteLeafMeetSupport_leaf H L a ha
  have hLeafBound : ∀ a : Nat, a ∈ L →
      f a ≤ max 2 (L.sup f) := by
    intro a ha
    have hSup : f a ≤ L.sup f := Finset.le_sup ha
    omega
  change u ∈ (Finset.range 3 ∪ L) ∪
    (finiteOneMeetSupport H L ∪ finiteTwoMeetSupport H L) at hu
  rcases Finset.mem_union.mp hu with hFront | hMeet
  · rcases Finset.mem_union.mp hFront with hMarker | hLeaf
    · have huSmall : u < 3 := Finset.mem_range.mp hMarker
      have hCases : u = 0 ∨ u = 1 ∨ u = 2 := by omega
      rcases hCases with h0 | h1 | h2
      · subst u
        rw [P.marker_zero]
        omega
      · subst u
        rw [P.marker_one]
        omega
      · subst u
        rw [P.marker_two]
        omega
    · exact hLeafBound u hLeaf
  · rcases Finset.mem_union.mp hMeet with hOne | hTwo
    · change u ∈ ((L.product L).filter
        (fun p : Nat × Nat => p.1 ≠ p.2)).image
          (fun p : Nat × Nat => H.oneMeetLevel p.1 p.2) at hOne
      obtain ⟨⟨a,b⟩,hPair,hEq⟩ := Finset.mem_image.mp hOne
      change H.oneMeetLevel a b = u at hEq
      obtain ⟨hPair,_hNe⟩ := Finset.mem_filter.mp hPair
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hPair
      have hA := hLeafBound a ha
      have hMeetEq : f (H.oneMeetLevel a b) =
          K.oneMeetLevel (f a) (f b) :=
        (P.leaf_oneMeet a b
          (hInSupport a ha) (hInSupport b hb)
          (hLLeaf a ha) (hLLeaf b hb)).symm
      have hMeetLe : K.oneMeetLevel (f a) (f b) ≤ f a :=
        (K.oneMeetLevel_le_min (f a) (f b)).trans
          (min_le_left _ _)
      calc
        f u = f (H.oneMeetLevel a b) := congrArg f hEq.symm
        _ = K.oneMeetLevel (f a) (f b) := hMeetEq
        _ ≤ f a := hMeetLe
        _ ≤ max 2 (L.sup f) := hA
    · change u ∈
        ((finiteOrderedLeafPairs L).product
          (finiteOrderedLeafPairs L)).image
          (fun p : (Nat × Nat) × (Nat × Nat) =>
            H.twoMeetLevel p.1.1 p.1.2 p.2.1 p.2.2) at hTwo
      obtain ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,hPair,hEq⟩ :=
        Finset.mem_image.mp hTwo
      change H.twoMeetLevel a b c d = u at hEq
      obtain ⟨hAB,hCD⟩ := Finset.mem_product.mp hPair
      obtain ⟨hAB,hab⟩ := Finset.mem_filter.mp hAB
      obtain ⟨hCD,hcd⟩ := Finset.mem_filter.mp hCD
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hAB
      obtain ⟨hc,hd⟩ := Finset.mem_product.mp hCD
      have hA := hLeafBound a ha
      have hMeetEq : f (H.twoMeetLevel a b c d) =
          K.twoMeetLevel (f a) (f b) (f c) (f d) :=
        (P.leaf_twoMeet a b c d
          (hInSupport a ha) (hInSupport b hb)
          (hInSupport c hc) (hInSupport d hd)
          hab hcd
          (hLLeaf a ha) (hLLeaf b hb)
          (hLLeaf c hc) (hLLeaf d hd)).symm
      have hMeetLe :
          K.twoMeetLevel (f a) (f b) (f c) (f d) ≤ f a :=
        (K.twoMeetLevel_le_min (f a) (f b) (f c) (f d)).trans
          (min_le_left _ _)
      calc
        f u = f (H.twoMeetLevel a b c d) := congrArg f hEq.symm
        _ = K.twoMeetLevel (f a) (f b) (f c) (f d) := hMeetEq
        _ ≤ f a := hMeetLe
        _ ≤ max 2 (L.sup f) := hA

/-- A finite target interval sufficient for every supported image
of any relative successor with one new selected source leaf.
This makes the search for SPLIT coordinates finite once the fresh
leaf image itself has been chosen. It does not construct that leaf. -/
theorem relative_successor_image_bound
    {g : Nat → Nat}
    (Q : AdmissibleCofinalDiaryStage H K F (m + 1) g)
    (hKeep : ∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
      g a = f a)
    (u : Nat) (hu : u ∈ countableDiaryFiniteSupport H (m + 1)) :
    g u ≤ max (max 2 ((countableDiaryLeafPrefix H m).sup f)) (g m) := by
  have hBound := Q.image_le_support_leaf_sup u hu
  have hSup :
      (countableDiaryLeafPrefix H (m + 1)).sup g ≤
        max ((countableDiaryLeafPrefix H m).sup f) (g m) := by
    apply Finset.sup_le
    intro a ha
    by_cases ham : a = m
    · subst a
      exact le_max_right _ _
    · obtain ⟨ha3,ham1,haLeaf⟩ :=
        (mem_countableDiaryLeafPrefix_iff H (m + 1) a).mp ha
      have haOld : a ∈ countableDiaryLeafPrefix H m :=
        (mem_countableDiaryLeafPrefix_iff H m a).mpr
          ⟨ha3, by omega,haLeaf⟩
      have hOld := hKeep a haOld
      have hOldBound : f a ≤ (countableDiaryLeafPrefix H m).sup f :=
        Finset.le_sup haOld
      omega
  omega

end AdmissibleCofinalDiaryStage
end DiaryLeafPriority
end ThreeUniformDiaries
