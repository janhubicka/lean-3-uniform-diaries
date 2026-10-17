import ThreeUniformDiaries.DiaryProtectedMixedTypeTransport
import ThreeUniformDiaries.TwoTypeMeetLevel

/-!
# Exact numerical auxiliary meets of split-containing pairs

For two ordered pairs each containing at least one actual split
vertex, the diary E edge shapes exclude EVERY positive auxiliary
test. Hence their auxiliary meet is explicitly either zero or the
cap at the lesser first coordinate. This is stronger than transport
of agreement at selected original cuts.

The one-pass old-vertex map copies marker-zero edges and is strictly
increasing. Therefore the full numerical auxiliary meet of every
such comparison is carried exactly to the old-vertex image.

Using the general two-type meet decomposition, the remaining
protected mixed full-meet obligation is reduced to exact transport
of the TWO coordinate singleton meets. Those separate hypotheses
are NOT discharged here. In particular no arbitrary protected
copy or every-flip absorption result is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- The numerical auxiliary meet of two mixed pairs is entirely
determined by their zero-marker incidence and the capping level.
No ordering or leaf-meet axioms are needed for this identity. -/
theorem RolePrediary.mixed_auxMeet_eq_cap_of_marker_agree
    (P : RolePrediary H) (a b c d : Nat)
    (hAB : IsDiarySplit H a ∨ IsDiarySplit H b)
    (hCD : IsDiarySplit H c ∨ IsDiarySplit H d)
    (hZero : H.edge 0 a b ↔ H.edge 0 c d) :
    H.auxMeetLevel a b c d = min a c := by
  apply le_antisymm (H.auxMeetLevel_le_min a b c d)
  have hAgree : H.SameAuxTypeBelow (min a c) a b c d := by
    intro x hx
    by_cases hxZero : x = 0
    · subst x
      exact hZero
    · have hxPos : 0 < x := by omega
      exact P.mixed_pairs_positive_aux_agree
        a b c d (min a c) hAB hCD x hxPos hx
  exact Nat.le_findGreatest (le_refl _) hAgree

/-- A disagreement at marker zero forces the mixed auxiliary
meet to be zero, independently of the cap. -/
theorem RolePrediary.mixed_auxMeet_eq_zero_of_marker_disagree
    (P : RolePrediary H) (a b c d : Nat)
    (hAB : IsDiarySplit H a ∨ IsDiarySplit H b)
    (hCD : IsDiarySplit H c ∨ IsDiarySplit H d)
    (hZero : ¬ (H.edge 0 a b ↔ H.edge 0 c d)) :
    H.auxMeetLevel a b c d = 0 := by
  have hMeetZero : H.auxMeetLevel a b c d ≤ 0 := by
    by_contra hNot
    have hPositive : 0 < H.auxMeetLevel a b c d := by omega
    exact hZero ((H.auxMeetLevel_agree a b c d) hPositive)
  omega

/-- The strictly increasing old-vertex enumeration commutes with
binary minimum, even though its image need not be convex. -/
theorem onePassOldImage_min
    (H : Ordered3Graph Nat) (u v : Nat) :
    onePassOldImage H (min u v) =
      min (onePassOldImage H u) (onePassOldImage H v) := by
  have hmono := (onePassOldImage_strictMono H).monotone
  rcases le_total u v with huv | hvu
  · simp [min_eq_left huv, min_eq_left (hmono huv)]
  · simp [min_eq_right hvu, min_eq_right (hmono hvu)]

/-- EXACT numerical auxiliary meet preservation, for arbitrary
split-containing source pairs, along the genuine one-pass old copy.
No source S1/S2 and no selected-cut/gap premise is required. -/
theorem onePass_mixed_auxMeet_preserved
    (P : RolePrediary H) (a b c d : Nat)
    (hAB : IsDiarySplit H a ∨ IsDiarySplit H b)
    (hCD : IsDiarySplit H c ∨ IsDiarySplit H d) :
    (onePassRawTarget H).auxMeetLevel
      (onePassOldImage H a) (onePassOldImage H b)
      (onePassOldImage H c) (onePassOldImage H d) =
      onePassOldImage H (H.auxMeetLevel a b c d) := by
  let G := onePassRawTarget H
  have hABTarget :
      IsDiarySplit G (onePassOldImage H a) ∨
      IsDiarySplit G (onePassOldImage H b) := by
    rcases hAB with ha | hb
    · exact Or.inl ((onePassOldImage_isDiarySplit H a).mp ha)
    · exact Or.inr ((onePassOldImage_isDiarySplit H b).mp hb)
  have hCDTarget :
      IsDiarySplit G (onePassOldImage H c) ∨
      IsDiarySplit G (onePassOldImage H d) := by
    rcases hCD with hc | hd
    · exact Or.inl ((onePassOldImage_isDiarySplit H c).mp hc)
    · exact Or.inr ((onePassOldImage_isDiarySplit H d).mp hd)
  have hABZero :
      G.edge 0 (onePassOldImage H a) (onePassOldImage H b) ↔
      H.edge 0 a b := by
    simpa only [onePassOldImage_zero] using
      (onePassRawTarget_edge_image_iff H 0 a b)
  have hCDZero :
      G.edge 0 (onePassOldImage H c) (onePassOldImage H d) ↔
      H.edge 0 c d := by
    simpa only [onePassOldImage_zero] using
      (onePassRawTarget_edge_image_iff H 0 c d)
  have hZeroTransport :
      (G.edge 0 (onePassOldImage H a) (onePassOldImage H b) ↔
       G.edge 0 (onePassOldImage H c) (onePassOldImage H d)) ↔
      (H.edge 0 a b ↔ H.edge 0 c d) := by
    constructor
    · intro h
      exact hABZero.symm.trans (h.trans hCDZero)
    · intro h
      exact hABZero.trans (h.trans hCDZero.symm)
  by_cases hZero : (H.edge 0 a b ↔ H.edge 0 c d)
  · have hZeroTarget :
        G.edge 0 (onePassOldImage H a) (onePassOldImage H b) ↔
        G.edge 0 (onePassOldImage H c) (onePassOldImage H d) :=
      hZeroTransport.mpr hZero
    rw [
      (onePassRawTarget_isPrediary P).mixed_auxMeet_eq_cap_of_marker_agree
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d)
        hABTarget hCDTarget hZeroTarget,
      P.mixed_auxMeet_eq_cap_of_marker_agree a b c d hAB hCD hZero]
    exact (onePassOldImage_min H a c).symm
  · have hZeroTarget :
        ¬ (G.edge 0 (onePassOldImage H a) (onePassOldImage H b) ↔
          G.edge 0 (onePassOldImage H c) (onePassOldImage H d)) :=
      fun h => hZero (hZeroTransport.mp h)
    rw [
      (onePassRawTarget_isPrediary P).mixed_auxMeet_eq_zero_of_marker_disagree
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d)
        hABTarget hCDTarget hZeroTarget,
      P.mixed_auxMeet_eq_zero_of_marker_disagree a b c d hAB hCD hZero]
    exact (onePassOldImage_zero H).symm

/-- For split-containing ordered pairs, preservation of the two
coordinate singleton meet LEVELS entails preservation of their
complete numerical two-type meet. The auxiliary hypothesis has been
discharged above; this theorem deliberately makes the remaining
coordinate obligations visible rather than assuming a protected
embedding or S1/S2 of the whole input. -/
theorem onePass_mixed_twoMeet_of_coordinate_meets
    (P : RolePrediary H) (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (hAB : IsDiarySplit H a ∨ IsDiarySplit H b)
    (hCD : IsDiarySplit H c ∨ IsDiarySplit H d)
    (hFirst :
      (onePassRawTarget H).oneMeetLevel
        (onePassOldImage H a) (onePassOldImage H c) =
        onePassOldImage H (H.oneMeetLevel a c))
    (hSecond :
      (onePassRawTarget H).oneMeetLevel
        (onePassOldImage H b) (onePassOldImage H d) =
        onePassOldImage H (H.oneMeetLevel b d)) :
    (onePassRawTarget H).twoMeetLevel
      (onePassOldImage H a) (onePassOldImage H b)
      (onePassOldImage H c) (onePassOldImage H d) =
      onePassOldImage H (H.twoMeetLevel a b c d) := by
  have hfAB := (onePassOldImage_strictMono H) hab
  have hfCD := (onePassOldImage_strictMono H) hcd
  rw [(onePassRawTarget H).twoMeetLevel_eq_min
      (onePassOldImage H a) (onePassOldImage H b)
      (onePassOldImage H c) (onePassOldImage H d)
      hfAB hfCD,
    H.twoMeetLevel_eq_min a b c d hab hcd]
  rw [onePass_mixed_auxMeet_preserved P a b c d hAB hCD,
      hFirst, hSecond]
  simp only [onePassOldImage_min]

end DiaryLeafPriority
end ThreeUniformDiaries
