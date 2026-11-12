import ThreeUniformDiaries.DiaryCandidateGeneratorRowsSameColour

/-!
# Track C: finite generator-table functionality is invariant within an old-cut colour

English proof and adversarial audit:
  janhubicka/3-uniform-diaries PR #317

For a true next source leaf m, the complete S1/S2 generator row
relation has EXACTLY ONE source-m row: the prescribed selected
leaf value (m,v). No meet row can have source m, since all
meet generators involving m are capped by some old selected
source leaf strictly below m.

The already established colour-equivalence theorem makes ALL
other rows literally identical for v,w >= the old-stage cut
with the same COMPLETE mixed singleton colour. Therefore
functionality transfers both ways and the functional canonical
candidate maps agree at EVERY non-m source coordinate on the
whole generated support, without a second functionality or
same-nonleaf-profile hypothesis.

This does not construct a functional candidate, preserve target
role/order/E2/E3/reserve by itself, or establish all-horizon
relative diary persistence.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The ONLY finite generator-table row whose SOURCE coordinate is
the new true leaf m is its explicitly prescribed leaf row (m,v).
Every singleton meet involving distinct selected leaves has a
strictly earlier selected first/second leaf, and every full ordered
pair meet is capped by a strictly earlier first source leaf.

This is true in ANY ordered source/target 3-graphs and requires
neither functional generator tables nor RoleDiary axioms. -/
theorem candidate_generator_row_at_new_leaf_iff
    {H K : Ordered3Graph Nat} {m : Nat}
    (hm : IsLeaf H m) (f : Nat → Nat) (v z : Nat) :
    ((m,z) ∈ candidateNewLeafGeneratorTable H K m f v ↔ z = v) := by
  classical
  let L := countableDiaryLeafPrefix H (m + 1)
  let q := candidateLeafImage f m v
  have hSourceBound (a : Nat) (ha : a ∈ L) : a ≤ m := by
    have hInfo := (mem_countableDiaryLeafPrefix_iff H (m + 1) a).mp ha
    omega
  constructor
  · intro hRow
    change (m,z) ∈ finiteLeafGeneratorTable H K L q at hRow
    unfold finiteLeafGeneratorTable at hRow
    rcases Finset.mem_union.mp hRow with hFront | hMeets
    · rcases Finset.mem_union.mp hFront with hMarker | hLeaf
      · obtain ⟨a,ha,hEq⟩ := Finset.mem_image.mp hMarker
        have hSource : a = m := by
          simpa using congrArg Prod.fst hEq
        have ha3 : a < 3 := Finset.mem_range.mp ha
        have hm3 : 3 ≤ m := hm.1
        omega
      · obtain ⟨a,ha,hEq⟩ := Finset.mem_image.mp hLeaf
        have hSource : a = m := by
          simpa using congrArg Prod.fst hEq
        have hValue : q a = z := by
          simpa using congrArg Prod.snd hEq
        rw [hSource] at hValue
        simpa [q,candidateLeafImage] using hValue.symm
    · rcases Finset.mem_union.mp hMeets with hOne | hTwo
      · obtain ⟨⟨a,b⟩,hp,hEq⟩ := Finset.mem_image.mp hOne
        obtain ⟨hp,hNe⟩ := Finset.mem_filter.mp hp
        obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
        have hSource : H.oneMeetLevel a b = m := by
          simpa using congrArg Prod.fst hEq
        have haLe : a ≤ m := hSourceBound a ha
        have hbLe : b ≤ m := hSourceBound b hb
        have haCap : H.oneMeetLevel a b ≤ a :=
          (H.oneMeetLevel_le_min a b).trans (min_le_left _ _)
        have hbCap : H.oneMeetLevel a b ≤ b :=
          (H.oneMeetLevel_le_min a b).trans (min_le_right _ _)
        omega
      · obtain ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,hp,hEq⟩ :=
          Finset.mem_image.mp hTwo
        obtain ⟨hAB,_hCD⟩ := Finset.mem_product.mp hp
        obtain ⟨hAB,hab⟩ := Finset.mem_filter.mp hAB
        obtain ⟨ha,hb⟩ := Finset.mem_product.mp hAB
        have hSource : H.twoMeetLevel a b c d = m := by
          simpa using congrArg Prod.fst hEq
        have hbBound : b ≤ m := hSourceBound b hb
        have hCap : H.twoMeetLevel a b c d ≤ a :=
          (H.twoMeetLevel_le_min a b c d).trans (min_le_left _ _)
        have hab' : a < b := by simpa only using hab
        have haLtM : a < m := lt_of_lt_of_le hab' hbBound
        have hmLeA : m ≤ a := by
          rw [← hSource]
          exact hCap
        exact (not_lt_of_ge hmLeA) haLtM
  · intro hz
    subst z
    have hmL : m ∈ L :=
      (mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
        ⟨hm.1, by omega, hm⟩
    change (m,v) ∈ finiteLeafGeneratorTable H K L q
    have hRow := finiteLeafGeneratorTable_leaf H K L q m hmL
    simpa only [q,candidateLeafImage,if_pos] using hRow

/-- Complete mixed singleton B-colour equality above the
old-stage-fixed cut makes FINITE table functionality an invariant:
if either proposed candidate table is functional, so is the other.

The rows away from m are identical WITHOUT functionality; the
sole row at m has value v or w. Thus collisions at every source
coordinate agree in the two tables. -/
theorem candidate_generator_functional_iff_of_oldCut_colour
    {H K : Ordered3Graph Nat} {m : Nat}
    (hm : IsLeaf H m) (f : Nat → Nat) (v w : Nat)
    (hv : oldStageTailCut H m f ≤ v)
    (hw : oldStageTailCut H m f ≤ w)
    (hColour :
      DiaryLowerBoundColors.singletonColour K (oldStageTailCut H m f) v =
        DiaryLowerBoundColors.singletonColour K (oldStageTailCut H m f) w) :
    FiniteGeneratorTableFunctional
      (candidateNewLeafGeneratorTable H K m f v) ↔
    FiniteGeneratorTableFunctional
      (candidateNewLeafGeneratorTable H K m f w) := by
  constructor
  · intro hFun u z₁ z₂ h₁ h₂
    by_cases hum : u = m
    · subst u
      exact
        ((candidate_generator_row_at_new_leaf_iff hm f w z₁).mp h₁).trans
          ((candidate_generator_row_at_new_leaf_iff hm f w z₂).mp h₂).symm
    · have hEq₁ :=
        (candidate_generator_row_other_iff_of_oldCut_colour
          hm f v w hv hw hColour u z₁ hum).mpr h₁
      have hEq₂ :=
        (candidate_generator_row_other_iff_of_oldCut_colour
          hm f v w hv hw hColour u z₂ hum).mpr h₂
      exact hFun u z₁ z₂ hEq₁ hEq₂
  · intro hFun u z₁ z₂ h₁ h₂
    by_cases hum : u = m
    · subst u
      exact
        ((candidate_generator_row_at_new_leaf_iff hm f v z₁).mp h₁).trans
          ((candidate_generator_row_at_new_leaf_iff hm f v z₂).mp h₂).symm
    · have hEq₁ :=
        (candidate_generator_row_other_iff_of_oldCut_colour
          hm f v w hv hw hColour u z₁ hum).mp h₁
      have hEq₂ :=
        (candidate_generator_row_other_iff_of_oldCut_colour
          hm f v w hv hw hColour u z₂ hum).mp h₂
      exact hFun u z₁ z₂ hEq₁ hEq₂

/-- Under ONE functional candidate, a proposed new target image
w of the same complete old-cut colour has a functional table
automatically, and the two canonical candidate maps agree at
EVERY supported source coordinate other than the new leaf m.

The canonical selected-leaf images at m are exactly v,w; no
separate second-table functionality or same-nonleaf-profile
hypothesis is needed. This is a finite NUMERIC theorem, not
an induced finite candidate or reserved extension. -/
theorem candidate_generator_maps_same_nonleaf_of_oldCut_colour
    {H K : Ordered3Graph Nat} {m : Nat}
    (hm : IsLeaf H m) (f : Nat → Nat) (v w : Nat)
    (hv : oldStageTailCut H m f ≤ v)
    (hw : oldStageTailCut H m f ≤ w)
    (hColour :
      DiaryLowerBoundColors.singletonColour K (oldStageTailCut H m f) v =
        DiaryLowerBoundColors.singletonColour K (oldStageTailCut H m f) w)
    (hFunV : FiniteGeneratorTableFunctional
      (candidateNewLeafGeneratorTable H K m f v)) :
    FiniteGeneratorTableFunctional
        (candidateNewLeafGeneratorTable H K m f w) ∧
    (∀ u : Nat, u ∈ countableDiaryFiniteSupport H (m+1) →
      u ≠ m →
      candidateNewLeafTableMap H K m f v u =
        candidateNewLeafTableMap H K m f w u) ∧
    candidateNewLeafTableMap H K m f v m = v ∧
    candidateNewLeafTableMap H K m f w m = w := by
  classical
  have hFunW : FiniteGeneratorTableFunctional
      (candidateNewLeafGeneratorTable H K m f w) :=
    (candidate_generator_functional_iff_of_oldCut_colour
      hm f v w hv hw hColour).mp hFunV
  refine ⟨hFunW, ?_, ?_, ?_⟩
  · intro u hu hum
    let L := countableDiaryLeafPrefix H (m+1)
    have hSupport : u ∈ finiteLeafMeetSupport H L := hu
    obtain ⟨z,hRow⟩ :=
      finiteLeafGeneratorTable_covers_support
        H K L (candidateLeafImage f m v) u hSupport
    have hRowW : (u,z) ∈ candidateNewLeafGeneratorTable H K m f w :=
      (candidate_generator_row_other_iff_of_oldCut_colour
        hm f v w hv hw hColour u z hum).mp hRow
    calc
      candidateNewLeafTableMap H K m f v u = z :=
        finiteGeneratorTableValue_eq_of_mem
          _ hFunV u z hRow
      _ = candidateNewLeafTableMap H K m f w u :=
        (finiteGeneratorTableValue_eq_of_mem
          _ hFunW u z hRowW).symm
  · have hmRow :
        (m,v) ∈ candidateNewLeafGeneratorTable H K m f v :=
      (candidate_generator_row_at_new_leaf_iff hm f v v).mpr rfl
    exact finiteGeneratorTableValue_eq_of_mem
      _ hFunV m v hmRow
  · have hmRow :
        (m,w) ∈ candidateNewLeafGeneratorTable H K m f w :=
      (candidate_generator_row_at_new_leaf_iff hm f w w).mpr rfl
    exact finiteGeneratorTableValue_eq_of_mem
      _ hFunW m w hmRow

end DiaryLeafPriority
end ThreeUniformDiaries
