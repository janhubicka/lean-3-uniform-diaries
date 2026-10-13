import ThreeUniformDiaries.TwoTypeMeetLevel
import Mathlib

/-!
# Diary leaf-pair split priority

This verifies the numerical consequence of diary axioms (S1), (S2):
full pair meets are the minimum of the auxiliary meet and two
coordinate singleton meets. The full meet is either the cap, 1,
or a 2-split, while the coordinate meets are 1-splits or leaves.

The separate structural bridge from the hypergraph diary axioms to
PairPattern, and the ATR pointed-envelope lemma, remain to be proved.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

private theorem full_eq_aux_of_before_coordinates
    {full aux first second : ℕ}
    (hmeet : full = min aux (min first second))
    (hf : full < first) (hs : full < second) :
    full = aux := by
  have hcoord : full < min first second := lt_min hf hs
  have hauxle : full ≤ aux := by
    rw [hmeet]
    exact min_le_left _ _
  by_contra hne
  have hauxgt : full < aux := by omega
  have hcontr : full < min aux (min first second) :=
    lt_min hauxgt hcoord
  omega

/-- Meet data of two pairs of diary leaves, retaining exactly the
role consequences required by the split-priority argument. -/
structure PairPattern where
  full : ℕ
  aux : ℕ
  first : ℕ
  second : ℕ
  cap : ℕ
  isTwoSplit : ℕ → Prop
  meet_decomposition : full = min aux (min first second)
  aux_le_cap : aux ≤ cap
  diary_cases : full = cap ∨ full = 1 ∨ isTwoSplit full
  first_after_marker : 1 < first
  second_after_marker : 1 < second
  first_not_twoSplit : ¬ isTwoSplit first
  second_not_twoSplit : ¬ isTwoSplit second

namespace PairPattern

/-- An ordinary diary pair meet which is not capped precedes
both coordinate singleton meets. -/
theorem full_before_coordinates_of_not_cap
    (d : PairPattern) (hn : d.full ≠ d.cap) :
    d.full < d.first ∧ d.full < d.second := by
  rcases d.diary_cases with hcap | hone | htwo
  · exact (hn hcap).elim
  · have hmarker₀ := d.first_after_marker
    have hmarker₁ := d.second_after_marker
    constructor <;> omega
  · have hle₀ : d.full ≤ d.first := by
      calc
        d.full = min d.aux (min d.first d.second) := d.meet_decomposition
        _ ≤ min d.first d.second := min_le_right _ _
        _ ≤ d.first := min_le_left _ _
    have hle₁ : d.full ≤ d.second := by
      calc
        d.full = min d.aux (min d.first d.second) := d.meet_decomposition
        _ ≤ min d.first d.second := min_le_right _ _
        _ ≤ d.second := min_le_right _ _
    have hne₀ : d.full ≠ d.first := by
      intro he
      apply d.first_not_twoSplit
      rw [← he]
      exact htwo
    have hne₁ : d.full ≠ d.second := by
      intro he
      apply d.second_not_twoSplit
      rw [← he]
      exact htwo
    constructor <;> omega

/-- In a diary, full 2-type meets of pairs of leaves coincide
with their auxiliary meets. -/
theorem aux_eq_full (d : PairPattern) : d.aux = d.full := by
  by_cases hc : d.full = d.cap
  · have hfull_le_aux : d.full ≤ d.aux := by
      rw [d.meet_decomposition]
      exact min_le_left _ _
    have hcapBound := d.aux_le_cap
    omega
  · obtain ⟨hf, hs⟩ := d.full_before_coordinates_of_not_cap hc
    exact (full_eq_aux_of_before_coordinates d.meet_decomposition hf hs).symm

/-- Transfer of the leaf-pair auxiliary meet along a type-respecting
order embedding, allowing target indices omitted by the embedding. -/
theorem aux_transfer
    (d : PairPattern) (f : ℕ → ℕ) (hf : StrictMono f)
    {imageFull imageAux imageFirst imageSecond imageCap : ℕ}
    (hfull : imageFull = f d.full)
    (hfirst : imageFirst = f d.first)
    (hsecond : imageSecond = f d.second)
    (hcap : imageCap = f d.cap)
    (hdecomp : imageFull = min imageAux (min imageFirst imageSecond))
    (hauxcap : imageAux ≤ imageCap) :
    imageAux = f d.aux := by
  rw [d.aux_eq_full]
  by_cases hc : d.full = d.cap
  · have heq : imageFull = imageCap := by
      rw [hfull, hcap, hc]
    have hfull_le_aux : imageFull ≤ imageAux := by
      rw [hdecomp]
      exact min_le_left _ _
    omega
  · obtain ⟨hbeforeFirst, hbeforeSecond⟩ :=
      d.full_before_coordinates_of_not_cap hc
    have hf₀ : imageFull < imageFirst := by
      rw [hfull, hfirst]
      exact hf hbeforeFirst
    have hf₁ : imageFull < imageSecond := by
      rw [hfull, hsecond]
      exact hf hbeforeSecond
    have heq : imageFull = imageAux :=
      full_eq_aux_of_before_coordinates hdecomp hf₀ hf₁
    omega

end PairPattern

/-- The exact leaf-pair priority conclusion for the *actual edge-derived*
singleton, auxiliary, and full 2-type meet levels. Its hypotheses are
precisely the numerical role consequences (S1) and (S2) for a diary.
The structural verification of those hypotheses from a complete
diary definition will be a separate Lean theorem. -/
theorem auxMeetLevel_eq_twoMeetLevel_of_diary_cases
    (H : Ordered3Graph Nat) (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (isTwoSplit : Nat → Prop)
    (hcases : H.twoMeetLevel a b c d = min a c ∨
      H.twoMeetLevel a b c d = 1 ∨ isTwoSplit (H.twoMeetLevel a b c d))
    (hfirst : 1 < H.oneMeetLevel a c)
    (hsecond : 1 < H.oneMeetLevel b d)
    (hfirstNotTwo : ¬ isTwoSplit (H.oneMeetLevel a c))
    (hsecondNotTwo : ¬ isTwoSplit (H.oneMeetLevel b d)) :
    H.auxMeetLevel a b c d = H.twoMeetLevel a b c d := by
  let p : PairPattern := {
    full := H.twoMeetLevel a b c d
    aux := H.auxMeetLevel a b c d
    first := H.oneMeetLevel a c
    second := H.oneMeetLevel b d
    cap := min a c
    isTwoSplit := isTwoSplit
    meet_decomposition := H.twoMeetLevel_eq_min a b c d hab hcd
    aux_le_cap := H.auxMeetLevel_le_min a b c d
    diary_cases := hcases
    first_after_marker := hfirst
    second_after_marker := hsecond
    first_not_twoSplit := hfirstNotTwo
    second_not_twoSplit := hsecondNotTwo
  }
  exact p.aux_eq_full

/-- Auxiliary leaf-pair meet transfer across a type-respecting
map, expressed with the actual source/target meet functions.
The map need not have convex image. -/
theorem auxMeetLevel_preserved_of_diary_cases
    (H K : Ordered3Graph Nat) (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (isTwoSplit : Nat → Prop)
    (hcases : H.twoMeetLevel a b c d = min a c ∨
      H.twoMeetLevel a b c d = 1 ∨ isTwoSplit (H.twoMeetLevel a b c d))
    (hfirst : 1 < H.oneMeetLevel a c)
    (hsecond : 1 < H.oneMeetLevel b d)
    (hfirstNotTwo : ¬ isTwoSplit (H.oneMeetLevel a c))
    (hsecondNotTwo : ¬ isTwoSplit (H.oneMeetLevel b d))
    (f : Nat → Nat) (hf : StrictMono f)
    (hfull : K.twoMeetLevel (f a) (f b) (f c) (f d) =
      f (H.twoMeetLevel a b c d))
    (hfst : K.oneMeetLevel (f a) (f c) =
      f (H.oneMeetLevel a c))
    (hsnd : K.oneMeetLevel (f b) (f d) =
      f (H.oneMeetLevel b d)) :
    K.auxMeetLevel (f a) (f b) (f c) (f d) =
      f (H.auxMeetLevel a b c d) := by
  let p : PairPattern := {
    full := H.twoMeetLevel a b c d
    aux := H.auxMeetLevel a b c d
    first := H.oneMeetLevel a c
    second := H.oneMeetLevel b d
    cap := min a c
    isTwoSplit := isTwoSplit
    meet_decomposition := H.twoMeetLevel_eq_min a b c d hab hcd
    aux_le_cap := H.auxMeetLevel_le_min a b c d
    diary_cases := hcases
    first_after_marker := hfirst
    second_after_marker := hsecond
    first_not_twoSplit := hfirstNotTwo
    second_not_twoSplit := hsecondNotTwo
  }
  have hmin : min (f a) (f c) = f (min a c) := by
    rcases le_total a c with hac | hca
    · simp [min_eq_left hac, min_eq_left (hf.monotone hac)]
    · simp [min_eq_right hca, min_eq_right (hf.monotone hca)]
  exact p.aux_transfer f hf hfull hfst hsnd hmin
    (K.twoMeetLevel_eq_min (f a) (f b) (f c) (f d) (hf hab) (hf hcd))
    (K.auxMeetLevel_le_min (f a) (f b) (f c) (f d))

end DiaryLeafPriority
end ThreeUniformDiaries
