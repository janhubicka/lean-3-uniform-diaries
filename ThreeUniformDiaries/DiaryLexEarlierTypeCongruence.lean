import ThreeUniformDiaries.DiaryLexEarlierMiddleColumnCausality
import ThreeUniformDiaries.DiarySourceLexFirstAuxBit

/-!
# LexEarlier respects the earlier singleton type of its later argument

The causal column lemma proves that the lexicographic decision for (y,u)
does not depend on marker bits with middle coordinate >= y. Here we prove
a different, complementary fact: if u and v have identical singleton
type below s and y <= s < min(u,v), then their literal lexicographic
comparison against y coincides.

The proper-meet case uses the FULL pointed capped two-meet. Its
apparent capped case q=m is impossible: the already verified
first-difference lemma makes the pointed auxiliary meet strictly
smaller than m, without ANY edge-order or diary axioms.

The result is for any ordered-edge ternary graph, with no role or
diary hypotheses. It is a type-conditioned orientation congruence,
NOT unconditional prefix-uniformity for arbitrary later leaves.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Agreement of later singleton types below s makes comparisons
of the singleton types of a fixed earlier vertex y with u and v
identical through each cut l <= s. -/
theorem sameOneTypeBelow_right_congr
    (H : Ordered3Graph Nat) (s l y u v : Nat)
    (hls : l ≤ s)
    (hUV : H.SameOneTypeBelow s u v) :
    H.SameOneTypeBelow l y u ↔
      H.SameOneTypeBelow l y v := by
  constructor
  · intro h x z hxz hzl
    have hUVxz : H.edge x z u ↔ H.edge x z v :=
      hUV hxz (lt_of_lt_of_le hzl hls)
    exact (h hxz hzl).trans hUVxz
  · intro h x z hxz hzl
    have hUVxz : H.edge x z u ↔ H.edge x z v :=
      hUV hxz (lt_of_lt_of_le hzl hls)
    exact (h hxz hzl).trans hUVxz.symm

/-- In the pointed pair tests (m,y) against (m,u) or (m,v),
all singleton and auxiliary comparisons through l <= m
are the same when u and v have the same singleton type below s,
with m < s. -/
theorem sameTwoTypeBelow_pointed_right_congr
    (H : Ordered3Graph Nat) (s l m y u v : Nat)
    (hlm : l ≤ m) (hms : m < s)
    (hUV : H.SameOneTypeBelow s u v) :
    H.SameTwoTypeBelow l m y m u ↔
      H.SameTwoTypeBelow l m y m v := by
  have hOne := sameOneTypeBelow_right_congr H s l y u v
    (hlm.trans hms.le) hUV
  constructor
  · rintro ⟨hFirst,hSecond,hAux⟩
    refine ⟨hFirst, hOne.mp hSecond, ?_⟩
    intro x hxl
    have hx : x < m := lt_of_lt_of_le hxl hlm
    have hUVxm : H.edge x m u ↔ H.edge x m v :=
      hUV hx hms
    exact (hAux hxl).trans hUVxm
  · rintro ⟨hFirst,hSecond,hAux⟩
    refine ⟨hFirst, hOne.mpr hSecond, ?_⟩
    intro x hxl
    have hx : x < m := lt_of_lt_of_le hxl hlm
    have hUVxm : H.edge x m u ↔ H.edge x m v :=
      hUV hx hms
    exact (hAux hxl).trans hUVxm.symm

/-- Exact equality of the two capped singleton meets:
the later arguments u,v have the same type below s and
the earlier argument y lies at or below that cut. -/
theorem oneMeetLevel_right_congr
    (H : Ordered3Graph Nat) (s y u v : Nat)
    (hys : y ≤ s) (hyu : y < u) (hyv : y < v)
    (hUV : H.SameOneTypeBelow s u v) :
    H.oneMeetLevel y u = H.oneMeetLevel y v := by
  classical
  apply le_antisymm
  · have hBound : H.oneMeetLevel y u ≤ y := by
      simpa only [min_eq_left hyu.le] using H.oneMeetLevel_le_min y u
    have hAgree : H.SameOneTypeBelow (H.oneMeetLevel y u) y v :=
      (sameOneTypeBelow_right_congr H s (H.oneMeetLevel y u)
        y u v (hBound.trans hys) hUV).mp
        (H.oneMeetLevel_agree y u)
    have hCap : H.oneMeetLevel y u ≤ min y v := by
      simpa only [min_eq_left hyv.le] using hBound
    exact Nat.le_findGreatest hCap hAgree
  · have hBound : H.oneMeetLevel y v ≤ y := by
      simpa only [min_eq_left hyv.le] using H.oneMeetLevel_le_min y v
    have hAgree : H.SameOneTypeBelow (H.oneMeetLevel y v) y u :=
      (sameOneTypeBelow_right_congr H s (H.oneMeetLevel y v)
        y u v (hBound.trans hys) hUV).mpr
        (H.oneMeetLevel_agree y v)
    have hCap : H.oneMeetLevel y v ≤ min y u := by
      simpa only [min_eq_left hyu.le] using hBound
    exact Nat.le_findGreatest hCap hAgree

/-- The pointed full two-meet that appears in the literal
LexEarlier definition is equal for (m,y),(m,u) and
(m,y),(m,v), as long as m < s and u,v have matching
singleton types below s. -/
theorem twoMeetLevel_pointed_right_congr
    (H : Ordered3Graph Nat) (s m y u v : Nat)
    (hms : m < s)
    (hUV : H.SameOneTypeBelow s u v) :
    H.twoMeetLevel m y m u =
      H.twoMeetLevel m y m v := by
  classical
  apply le_antisymm
  · have hBound : H.twoMeetLevel m y m u ≤ m := by
      simpa only [min_self] using H.twoMeetLevel_le_min m y m u
    have hAgree : H.SameTwoTypeBelow
        (H.twoMeetLevel m y m u) m y m v :=
      (sameTwoTypeBelow_pointed_right_congr H s
        (H.twoMeetLevel m y m u) m y u v hBound hms hUV).mp
        (H.twoMeetLevel_agree m y m u)
    have hCap : H.twoMeetLevel m y m u ≤ min m m := by
      simpa only [min_self] using hBound
    exact Nat.le_findGreatest hCap hAgree
  · have hBound : H.twoMeetLevel m y m v ≤ m := by
      simpa only [min_self] using H.twoMeetLevel_le_min m y m v
    have hAgree : H.SameTwoTypeBelow
        (H.twoMeetLevel m y m v) m y m u :=
      (sameTwoTypeBelow_pointed_right_congr H s
        (H.twoMeetLevel m y m v) m y u v hBound hms hUV).mpr
        (H.twoMeetLevel_agree m y m v)
    have hCap : H.twoMeetLevel m y m v ≤ min m m := by
      simpa only [min_self] using hBound
    exact Nat.le_findGreatest hCap hAgree

/-- The literal lexicographic comparison has unconditional
type-congruence for arbitrary ternary edge predicates. The proper
singleton-meet case already enforces a strictly earlier pointed
two-meet, so no edge-order assumption is needed. -/
theorem lexEarlier_right_congr_of_sameOneType
    (H : Ordered3Graph Nat)
    (s y u v : Nat)
    (hys : y ≤ s) (hyu : y < u) (hyv : y < v)
    (hUV : H.SameOneTypeBelow s u v) :
    LexEarlier H y u ↔ LexEarlier H y v := by
  classical
  have hMeet : H.oneMeetLevel y u = H.oneMeetLevel y v :=
    oneMeetLevel_right_congr H s y u v hys hyu hyv hUV
  let m := H.oneMeetLevel y u
  have hmy : m ≤ y := by
    dsimp [m]
    simpa only [min_eq_left hyu.le] using H.oneMeetLevel_le_min y u
  by_cases hm : m < y
  · have hms : m < s := lt_of_lt_of_le hm hys
    have hTwo : H.twoMeetLevel m y m u =
        H.twoMeetLevel m y m v :=
      twoMeetLevel_pointed_right_congr H s m y u v hms hUV
    have hAuxLt : H.auxMeetLevel m y m u < m :=
      (onePass_source_mixedAux_first_difference
        H m y u hm (lt_trans hm hyu) (by dsimp [m])).1
    have hQLt : H.twoMeetLevel m y m v < m := by
      rw [← hTwo, H.twoMeetLevel_eq_min m y m u hm (lt_trans hm hyu)]
      exact lt_of_le_of_lt (min_le_left _ _) hAuxLt
    have hEdge :
        H.edge (H.twoMeetLevel m y m u) m u ↔
          H.edge (H.twoMeetLevel m y m v) m v := by
      rw [hTwo]
      exact hUV hQLt hms
    have hCore :
        ((y < u ∧ m = y) ∨
         (m < min y u ∧ H.edge (H.twoMeetLevel m y m u) m u)) ↔
        ((y < v ∧ m = y) ∨
         (m < min y v ∧ H.edge (H.twoMeetLevel m y m v) m v)) := by
      constructor
      · rintro (⟨_, hcap⟩ | ⟨_, he⟩)
        · exact Or.inl ⟨hyv,hcap⟩
        · exact Or.inr ⟨by omega,hEdge.mp he⟩
      · rintro (⟨_, hcap⟩ | ⟨_, he⟩)
        · exact Or.inl ⟨hyu,hcap⟩
        · exact Or.inr ⟨by omega,hEdge.mpr he⟩
    simpa only [LexEarlier, ← hMeet] using hCore
  · have hcap : m = y := by omega
    have hcapV : H.oneMeetLevel y v = y := hMeet.symm.trans hcap
    have hLeft : LexEarlier H y u := Or.inl ⟨hyu,hcap⟩
    have hRight : LexEarlier H y v := Or.inl ⟨hyv,hcapV⟩
    exact ⟨fun _ => hRight, fun _ => hLeft⟩

end DiaryLeafPriority
end ThreeUniformDiaries
