import ThreeUniformDiaries.DiaryOneOldCutColourAllNewMeets
import ThreeUniformDiaries.DiaryFiniteCandidateCriterion
import ThreeUniformDiaries.DiaryUniformOldStageTailColour

/-!
# Track C: complete old-cut colour controls literal generator table rows

English first and adversarial mathematical audit:
  janhubicka/3-uniform-diaries PR #317

For one genuine new SOURCE leaf m, any two proposed target images
v,w >= oldStageTailCut H m f with equal COMPLETE mixed singleton
colour determine literally the SAME marker, old-leaf, S1 and S2
generator rows on every supported source coordinate other than m.
The ONLY row with source coordinate m is the selected-leaf row
(m,v) or (m,w). No target RoleDiary, finite candidate legality,
future persistence or genericity is assumed in this deduction.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

private theorem oneMeetLevel_comm_for_table
    (K : Ordered3Graph Nat) (a b : Nat) :
    K.oneMeetLevel a b = K.oneMeetLevel b a := by
  classical
  have hAB : K.SameOneTypeBelow (K.oneMeetLevel a b) b a := by
    intro x y hxy hy
    exact ((K.oneMeetLevel_agree a b) hxy hy).symm
  have hBA : K.SameOneTypeBelow (K.oneMeetLevel b a) a b := by
    intro x y hxy hy
    exact ((K.oneMeetLevel_agree b a) hxy hy).symm
  apply Nat.le_antisymm
  · apply Nat.le_findGreatest
      (by simpa only [min_comm] using K.oneMeetLevel_le_min a b)
    exact hAB
  · apply Nat.le_findGreatest
      (by simpa only [min_comm] using K.oneMeetLevel_le_min b a)
    exact hBA

private theorem candidate_row_other_forward
    (H K : Ordered3Graph Nat) (m : Nat) (hm : IsLeaf H m)
    (f : Nat → Nat) (v w : Nat)
    (hv : oldStageTailCut H m f ≤ v)
    (hw : oldStageTailCut H m f ≤ w)
    (hColour :
      DiaryLowerBoundColors.singletonColour K (oldStageTailCut H m f) v =
        DiaryLowerBoundColors.singletonColour K (oldStageTailCut H m f) w)
    (u z : Nat) (hum : u ≠ m)
    (hRow : (u,z) ∈ candidateNewLeafGeneratorTable H K m f v) :
    (u,z) ∈ candidateNewLeafGeneratorTable H K m f w := by
  classical
  let L := countableDiaryLeafPrefix H (m + 1)
  let B := oldStageTailCut H m f
  let qv := candidateLeafImage f m v
  let qw := candidateLeafImage f m w
  have hSourceInfo (a : Nat) (ha : a ∈ L) : a ≤ m := by
    have h := (mem_countableDiaryLeafPrefix_iff H (m + 1) a).mp ha
    omega
  have hOldMember (a : Nat) (ha : a ∈ L) (ham : a ≠ m) :
      a ∈ countableDiaryLeafPrefix H m := by
    obtain ⟨ha3,ham1,hLeaf⟩ :=
      (mem_countableDiaryLeafPrefix_iff H (m + 1) a).mp ha
    exact (mem_countableDiaryLeafPrefix_iff H m a).mpr
      ⟨ha3, by omega, hLeaf⟩
  have hOldBound (a : Nat) (ha : a ∈ countableDiaryLeafPrefix H m) :
      f a < B := by
    have hSup : f a ≤ (countableDiaryLeafPrefix H m).sup f :=
      Finset.le_sup (f := f) ha
    change f a <
      max ((countableDiaryFiniteSupport H m).sup f)
        ((countableDiaryLeafPrefix H m).sup f) + 1
    omega
  have hSame : K.SameOneTypeBelow B v w :=
    (DiaryLowerBoundColors.singletonColour_eq_iff K B v w).mp hColour
  have hOneType (a : Nat) (ha : a ∈ L) :
      K.SameOneTypeBelow B (qv a) (qw a) := by
    by_cases ham : a = m
    · subst a
      simpa [qv,qw,candidateLeafImage] using hSame
    · have hEq : qv a = qw a := by
        simp [qv,qw,candidateLeafImage,ham]
      rw [hEq]
      intro x y hxy hy
      exact Iff.rfl
  have hOneValue (a b : Nat) (ha : a ∈ L) (hb : b ∈ L)
      (hab : a ≠ b) :
      K.oneMeetLevel (qv a) (qv b) =
        K.oneMeetLevel (qw a) (qw b) := by
    by_cases ham : a = m
    · subst a
      have hbm : b ≠ m := Ne.symm hab
      have hbOld := hOldMember b hb hbm
      have hbB := hOldBound b hbOld
      have hbv : f b < v := lt_of_lt_of_le hbB hv
      have hbw : f b < w := lt_of_lt_of_le hbB hw
      have hMeet := oneMeetLevel_eq_of_sameOneTypeBelow_cut
        K B (f b) v w hbB hbv hbw hSame
      calc
        K.oneMeetLevel (qv m) (qv b) = K.oneMeetLevel v (f b) := by
          simp [qv,candidateLeafImage,hbm]
        _ = K.oneMeetLevel (f b) v := oneMeetLevel_comm_for_table K v (f b)
        _ = K.oneMeetLevel (f b) w := hMeet
        _ = K.oneMeetLevel w (f b) := (oneMeetLevel_comm_for_table K w (f b)).symm
        _ = K.oneMeetLevel (qw m) (qw b) := by
          simp [qw,candidateLeafImage,hbm]
    · by_cases hbm : b = m
      · subst b
        have haOld := hOldMember a ha ham
        have haB := hOldBound a haOld
        have hav : f a < v := lt_of_lt_of_le haB hv
        have haw : f a < w := lt_of_lt_of_le haB hw
        have hMeet := oneMeetLevel_eq_of_sameOneTypeBelow_cut
          K B (f a) v w haB hav haw hSame
        simpa [qv,qw,candidateLeafImage,ham] using hMeet
      · simp [qv,qw,candidateLeafImage,ham,hbm]
  have hPairValue (a b c d : Nat)
      (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hd : d ∈ L)
      (hab : a < b) (hcd : c < d) :
      K.twoMeetLevel (qv a) (qv b) (qv c) (qv d) =
        K.twoMeetLevel (qw a) (qw b) (qw c) (qw d) := by
    have haLt : a < m := by
      have hbm := hSourceInfo b hb
      omega
    have hcLt : c < m := by
      have hdm := hSourceInfo d hd
      omega
    have haNe : a ≠ m := ne_of_lt haLt
    have hcNe : c ≠ m := ne_of_lt hcLt
    have haOld := hOldMember a ha haNe
    have hcOld := hOldMember c hc hcNe
    have haB := hOldBound a haOld
    have hcB := hOldBound c hcOld
    have hMeet := twoMeetLevel_eq_of_second_tail_types
      K B (f a) (f c) (qv b) (qw b) (qv d) (qw d)
      haB hcB (hOneType b hb) (hOneType d hd)
    simpa [qv,qw,candidateLeafImage,haNe,hcNe] using hMeet
  change (u,z) ∈ finiteLeafGeneratorTable H K L qv at hRow
  change (u,z) ∈ finiteLeafGeneratorTable H K L qw
  unfold finiteLeafGeneratorTable at hRow
  rcases Finset.mem_union.mp hRow with hFront | hMeet
  · rcases Finset.mem_union.mp hFront with hMarker | hLeaf
    · obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp hMarker
      rw [←hEq]
      exact finiteLeafGeneratorTable_marker H K L qw a
        (Finset.mem_range.mp ha)
    · obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp hLeaf
      have hau : a = u := by simpa using congrArg Prod.fst hEq
      have ham : a ≠ m := by simpa only [hau] using hum
      have hVal : qv a = qw a := by
        simp [qv,qw,candidateLeafImage,ham]
      rw [←hEq,hVal]
      exact finiteLeafGeneratorTable_leaf H K L qw a ha
  · rcases Finset.mem_union.mp hMeet with hOne | hTwo
    · obtain ⟨⟨a,b⟩, hp, hEq⟩ := Finset.mem_image.mp hOne
      obtain ⟨hp, hNe⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
      have hVal := hOneValue a b ha hb hNe
      rw [←hEq,hVal]
      exact finiteLeafGeneratorTable_oneMeet H K L qw a b ha hb hNe
    · obtain ⟨⟨⟨a,b⟩,⟨c,d⟩⟩, hp, hEq⟩ :=
        Finset.mem_image.mp hTwo
      obtain ⟨hpAB,hpCD⟩ := Finset.mem_product.mp hp
      obtain ⟨hpAB,hab⟩ := Finset.mem_filter.mp hpAB
      obtain ⟨hpCD,hcd⟩ := Finset.mem_filter.mp hpCD
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hpAB
      obtain ⟨hc,hd⟩ := Finset.mem_product.mp hpCD
      have hVal := hPairValue a b c d ha hb hc hd hab hcd
      rw [←hEq,hVal]
      exact finiteLeafGeneratorTable_twoMeet H K L qw a b c d
        ha hb hc hd hab hcd

/-- All rows of the two proposed generator tables OTHER THAN the new
source leaf m are literally identical, even before functionality. -/
theorem candidate_generator_row_other_iff_of_oldCut_colour
    {H K : Ordered3Graph Nat} {m : Nat} (hm : IsLeaf H m)
    (f : Nat → Nat) (v w : Nat)
    (hv : oldStageTailCut H m f ≤ v)
    (hw : oldStageTailCut H m f ≤ w)
    (hColour :
      DiaryLowerBoundColors.singletonColour K (oldStageTailCut H m f) v =
        DiaryLowerBoundColors.singletonColour K (oldStageTailCut H m f) w)
    (u z : Nat) (hum : u ≠ m) :
    ((u,z) ∈ candidateNewLeafGeneratorTable H K m f v ↔
      (u,z) ∈ candidateNewLeafGeneratorTable H K m f w) := by
  constructor
  · exact candidate_row_other_forward H K m hm f v w hv hw
      hColour u z hum
  · exact candidate_row_other_forward H K m hm f w v hw hv
      hColour.symm u z hum

end DiaryLeafPriority
end ThreeUniformDiaries
