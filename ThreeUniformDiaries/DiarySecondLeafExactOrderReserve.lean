import ThreeUniformDiaries.DiaryTwoLeafExactSixSupport
import ThreeUniformDiaries.DiaryFutureReserveFusion

/-!
# Exactly three gaps certify future-order reserve on two-leaf support

For the second selected source leaf, the previously established
literal support is the ordered six-point set

  0 < 1 < 2 < s < a < m

where s is the singleton meet of the two leaves a<m.
Fix any total candidate map g sending markers to themselves,
s to t, a to w and m to v.

Then the numerical FutureOrderReserve predicate on ALL supported
pairs is equivalent to just THREE adjacent numeric inequalities:

  s <= t,
  t + (a-s) <= w,
  w + (m-a) <= v.

This isolates the exact order/reserve part of the two-leaf
candidate realization problem. It does not prove induced edge
or nonedge preservation, and does not construct a suitable v.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Once the literal six-point source support and the images of
its coordinates have been fixed, future-order reserve is EXACTLY
the conjunction of three gap constraints. No assumption on
the target diary or its genericity is required for this numerical
iff theorem. -/
theorem RoleDiary.second_leaf_reserve_iff_three_gaps
    {H : Ordered3Graph Nat}
    (D : RoleDiary H)
    {a m : Nat}
    (ha : IsLeaf H a) (hm : IsLeaf H m)
    (ham : a < m)
    (hOld : countableDiaryLeafPrefix H m = {a})
    (g : Nat → Nat) (t w v : Nat)
    (hMarker : ∀ i : Nat, i < 3 → g i = i)
    (hMeetImage : g (H.oneMeetLevel a m) = t)
    (hA : g a = w) (hM : g m = v) :
    FutureOrderReserve H (m + 1) g ↔
      (H.oneMeetLevel a m ≤ t ∧
       t + (a - H.oneMeetLevel a m) ≤ w ∧
       w + (m - a) ≤ v) := by
  let s := H.oneMeetLevel a m
  have hsOne : IsOneSplit H s :=
    D.singleton_meets a m ha hm (ne_of_lt ham)
  have hs3 : 3 ≤ s := hsOne.1
  have hsLeA : s ≤ a :=
    (H.oneMeetLevel_le_min a m).trans (min_le_left _ _)
  have hsNeA : s ≠ a := by
    intro heq
    have hRole : IsOneSplit H a := by
      simpa only [heq] using hsOne
    exact ha.2.1 hRole.2.1
  have hSA : s < a := by omega
  have hSupport :
      countableDiaryFiniteSupport H (m + 1) =
        (Finset.range 3 ∪ ({a,m,s} : Finset Nat)) :=
    D.second_leaf_support_eq_six ha hm ham hOld
  have h2Mem :
      2 ∈ countableDiaryFiniteSupport H (m + 1) := by
    rw [hSupport]
    simp
  have hsMem :
      s ∈ countableDiaryFiniteSupport H (m + 1) := by
    rw [hSupport]
    simp
  have haMem :
      a ∈ countableDiaryFiniteSupport H (m + 1) := by
    rw [hSupport]
    simp
  have hmMem :
      m ∈ countableDiaryFiniteSupport H (m + 1) := by
    rw [hSupport]
    simp
  change FutureOrderReserve H (m + 1) g ↔
    (s ≤ t ∧ t + (a - s) ≤ w ∧ w + (m - a) ≤ v)
  constructor
  · intro hReserve
    have h2S := hReserve 2 s h2Mem hsMem (by omega)
    have hSA' := hReserve s a hsMem haMem hSA
    have hAM := hReserve a m haMem hmMem ham
    have h2Image : g 2 = 2 := hMarker 2 (by omega)
    have hsImage : g s = t := hMeetImage
    rw [h2Image,hsImage] at h2S
    rw [hsImage,hA] at hSA'
    rw [hA,hM] at hAM
    omega
  · rintro ⟨h2S,hSA',hAM⟩
    intro x y hx hy hxy
    have hxCases : x < 3 ∨ x = a ∨ x = m ∨ x = s := by
      rw [hSupport] at hx
      simpa only [Finset.mem_union, Finset.mem_range,
        Finset.mem_insert, Finset.mem_singleton] using hx
    have hyCases : y < 3 ∨ y = a ∨ y = m ∨ y = s := by
      rw [hSupport] at hy
      simpa only [Finset.mem_union, Finset.mem_range,
        Finset.mem_insert, Finset.mem_singleton] using hy
    have hxValue :
        (x < 3 ∧ g x = x) ∨
        (x = a ∧ g x = w) ∨
        (x = m ∧ g x = v) ∨
        (x = s ∧ g x = t) := by
      rcases hxCases with hSmall | hEq | hEq | hEq
      · exact Or.inl ⟨hSmall,hMarker x hSmall⟩
      · refine Or.inr (Or.inl ⟨hEq,?_⟩)
        simpa only [hEq] using hA
      · refine Or.inr (Or.inr (Or.inl ⟨hEq,?_⟩))
        simpa only [hEq] using hM
      · refine Or.inr (Or.inr (Or.inr ⟨hEq,?_⟩))
        simpa only [hEq] using hMeetImage
    have hyValue :
        (y < 3 ∧ g y = y) ∨
        (y = a ∧ g y = w) ∨
        (y = m ∧ g y = v) ∨
        (y = s ∧ g y = t) := by
      rcases hyCases with hSmall | hEq | hEq | hEq
      · exact Or.inl ⟨hSmall,hMarker y hSmall⟩
      · refine Or.inr (Or.inl ⟨hEq,?_⟩)
        simpa only [hEq] using hA
      · refine Or.inr (Or.inr (Or.inl ⟨hEq,?_⟩))
        simpa only [hEq] using hM
      · refine Or.inr (Or.inr (Or.inr ⟨hEq,?_⟩))
        simpa only [hEq] using hMeetImage
    rcases hxValue with hxMark | hxA | hxM | hxS
    all_goals rcases hyValue with hyMark | hyA | hyM | hyS
    all_goals omega

end DiaryLeafPriority
end ThreeUniformDiaries
