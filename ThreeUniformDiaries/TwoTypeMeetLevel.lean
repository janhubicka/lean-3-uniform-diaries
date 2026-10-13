import ThreeUniformDiaries.ExactTypeMeetLevels

/-!
# Exact full two-type meet decomposition

An ordinary 2-type over a cut is equivalent to the conjunction of the
two coordinate singleton types and its auxiliary type. This file
extracts the equality of the *literal capped meet indices* used by the
diary leaf-pair split-priority argument. No diary axioms are assumed.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Last agreement cut for full two-types, capped at the lesser
first coordinate of the two ordered pairs. -/
noncomputable def twoMeetLevel (H : Ordered3Graph Nat)
    (u₀ u₁ v₀ v₁ : Nat) : Nat := by
  classical
  exact Nat.findGreatest
    (fun l => H.SameTwoTypeBelow l u₀ u₁ v₀ v₁) (min u₀ v₀)

theorem twoMeetLevel_le_min (H : Ordered3Graph Nat)
    (u₀ u₁ v₀ v₁ : Nat) :
    H.twoMeetLevel u₀ u₁ v₀ v₁ ≤ min u₀ v₀ := by
  classical
  exact Nat.findGreatest_le
    (P := fun l => H.SameTwoTypeBelow l u₀ u₁ v₀ v₁) (min u₀ v₀)

theorem twoMeetLevel_agree (H : Ordered3Graph Nat)
    (u₀ u₁ v₀ v₁ : Nat) :
    H.SameTwoTypeBelow (H.twoMeetLevel u₀ u₁ v₀ v₁)
      u₀ u₁ v₀ v₁ := by
  classical
  unfold twoMeetLevel
  apply Nat.findGreatest_spec
    (P := fun l => H.SameTwoTypeBelow l u₀ u₁ v₀ v₁)
    (m := 0) (n := min u₀ v₀)
  · omega
  · refine ⟨?_, ?_, ?_⟩
    · intro a b hab hb
      omega
    · intro a b hab hb
      omega
    · intro a ha
      omega

/-- Exact decomposition of an ordinary full two-type meet into
the auxiliary and two coordinate singleton meets. -/
theorem twoMeetLevel_eq_min (H : Ordered3Graph Nat)
    (u₀ u₁ v₀ v₁ : Nat)
    (hu : u₀ < u₁) (hv : v₀ < v₁) :
    H.twoMeetLevel u₀ u₁ v₀ v₁ =
      min (H.auxMeetLevel u₀ u₁ v₀ v₁)
        (min (H.oneMeetLevel u₀ v₀) (H.oneMeetLevel u₁ v₁)) := by
  classical
  let t := H.twoMeetLevel u₀ u₁ v₀ v₁
  let w := min (H.auxMeetLevel u₀ u₁ v₀ v₁)
    (min (H.oneMeetLevel u₀ v₀) (H.oneMeetLevel u₁ v₁))
  have htBound : t ≤ min u₀ v₀ := H.twoMeetLevel_le_min u₀ u₁ v₀ v₁
  have htBoundSecond : t ≤ min u₁ v₁ := by
    apply le_min
    · exact (htBound.trans (min_le_left _ _)).trans hu.le
    · exact (htBound.trans (min_le_right _ _)).trans hv.le
  have hTypes : H.SameTwoTypeBelow t u₀ u₁ v₀ v₁ :=
    H.twoMeetLevel_agree u₀ u₁ v₀ v₁
  have htAux : t ≤ H.auxMeetLevel u₀ u₁ v₀ v₁ := by
    apply Nat.le_findGreatest htBound
    exact hTypes.2.2
  have htOne0 : t ≤ H.oneMeetLevel u₀ v₀ := by
    apply Nat.le_findGreatest htBound
    exact hTypes.1
  have htOne1 : t ≤ H.oneMeetLevel u₁ v₁ := by
    apply Nat.le_findGreatest htBoundSecond
    exact hTypes.2.1
  have htLeW : t ≤ w := le_min htAux (le_min htOne0 htOne1)
  have hwAux : w ≤ H.auxMeetLevel u₀ u₁ v₀ v₁ := min_le_left _ _
  have hwOne0 : w ≤ H.oneMeetLevel u₀ v₀ :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hwOne1 : w ≤ H.oneMeetLevel u₁ v₁ :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hwBound : w ≤ min u₀ v₀ :=
    hwAux.trans (H.auxMeetLevel_le_min u₀ u₁ v₀ v₁)
  have hwAgreeOne0 : H.SameOneTypeBelow w u₀ v₀ := by
    have hp := H.oneMeetLevel_agree u₀ v₀
    intro a b hab hb
    exact hp hab (lt_of_lt_of_le hb hwOne0)
  have hwAgreeOne1 : H.SameOneTypeBelow w u₁ v₁ := by
    have hp := H.oneMeetLevel_agree u₁ v₁
    intro a b hab hb
    exact hp hab (lt_of_lt_of_le hb hwOne1)
  have hwAgreeAux : H.SameAuxTypeBelow w u₀ u₁ v₀ v₁ := by
    have hp := H.auxMeetLevel_agree u₀ u₁ v₀ v₁
    intro a ha
    exact hp (lt_of_lt_of_le ha hwAux)
  have hwAgree : H.SameTwoTypeBelow w u₀ u₁ v₀ v₁ :=
    ⟨hwAgreeOne0, hwAgreeOne1, hwAgreeAux⟩
  have hwLeT : w ≤ t := Nat.le_findGreatest hwBound hwAgree
  exact Nat.le_antisymm htLeW hwLeT

end Ordered3Graph
end ThreeUniformDiaries
