import ThreeUniformDiaries.DiaryTwoTailTypeATR

/-!
# Finite selected carriers closed under both diary type meets

An ATR-admissible finite initial carrier preserves singleton and
auxiliary pair meets. The decomposition of ordinary full 2-type
meets shows that it consequently preserves *all* ordinary
singleton and pair meets. Therefore its image is meet-closed.

This isolates the abstract closure argument from the diary
two-tail/three-tail case distinction. In particular, no claim
about arbitrary mixed auxiliary meet preservation is used.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Ordinary closure under singleton and full ordered-pair meets. -/
def IsMeetClosed (K : Ordered3Graph Nat) (S : Set Nat) : Prop :=
  (∀ u v, u ∈ S → v ∈ S → K.oneMeetLevel u v ∈ S) ∧
  (∀ a b c d, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a < b → c < d → K.twoMeetLevel a b c d ∈ S)

/-- Image of precisely the first `limit` vertices under an
enumeration `f` (the enumerator need not be onto). -/
def selectedCarrier (f : Nat → Nat) (limit : Nat) : Set Nat :=
  {v | ∃ t, t < limit ∧ f t = v}

/-- Exact full two-type meets follow from exact singleton and
auxiliary meets by the literal capped-meet decomposition. -/
theorem selected_full_twoMeet_preserved
    (K : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (limit : Nat)
    (hone : ∀ u v, u < limit → v < limit →
      K.oneMeetLevel (f u) (f v) =
        f ((K.pullback f).oneMeetLevel u v))
    (haux : ∀ a b c d, a < b → c < d →
      b < limit → d < limit →
      K.auxMeetLevel (f a) (f b) (f c) (f d) =
        f ((K.pullback f).auxMeetLevel a b c d))
    (a b c d : Nat) (hab : a < b) (hcd : c < d)
    (hb : b < limit) (hd : d < limit) :
    K.twoMeetLevel (f a) (f b) (f c) (f d) =
      f ((K.pullback f).twoMeetLevel a b c d) := by
  have ha : a < limit := lt_trans hab hb
  have hc : c < limit := lt_trans hcd hd
  have hmin (s t : Nat) : min (f s) (f t) = f (min s t) := by
    rcases le_total s t with hst | hts
    · simp [min_eq_left hst, min_eq_left (hf.monotone hst)]
    · simp [min_eq_right hts, min_eq_right (hf.monotone hts)]
  calc
    K.twoMeetLevel (f a) (f b) (f c) (f d) =
      min (K.auxMeetLevel (f a) (f b) (f c) (f d))
        (min (K.oneMeetLevel (f a) (f c))
             (K.oneMeetLevel (f b) (f d))) :=
      K.twoMeetLevel_eq_min (f a) (f b) (f c) (f d)
        (hf hab) (hf hcd)
    _ = min (f ((K.pullback f).auxMeetLevel a b c d))
          (min (f ((K.pullback f).oneMeetLevel a c))
               (f ((K.pullback f).oneMeetLevel b d))) := by
      rw [haux a b c d hab hcd hb hd,
        hone a c ha hc, hone b d hb hd]
    _ = f (min ((K.pullback f).auxMeetLevel a b c d)
        (min ((K.pullback f).oneMeetLevel a c)
             ((K.pullback f).oneMeetLevel b d))) := by
      simp only [hmin]
    _ = f ((K.pullback f).twoMeetLevel a b c d) := by
      rw [(K.pullback f).twoMeetLevel_eq_min a b c d hab hcd]

/-- Exact finite ATR meet preservation implies that the selected
carrier is closed under both ordinary 1-type and full 2-type meets. -/
theorem selectedCarrier_meet_closed_of_ATR
    (K : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (limit : Nat)
    (hone : ∀ u v, u < limit → v < limit →
      K.oneMeetLevel (f u) (f v) =
        f ((K.pullback f).oneMeetLevel u v))
    (haux : ∀ a b c d, a < b → c < d →
      b < limit → d < limit →
      K.auxMeetLevel (f a) (f b) (f c) (f d) =
        f ((K.pullback f).auxMeetLevel a b c d)) :
    K.IsMeetClosed (selectedCarrier f limit) := by
  constructor
  · intro u v hu hv
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨y, hy, rfl⟩ := hv
    refine ⟨(K.pullback f).oneMeetLevel x y, ?_, ?_⟩
    · have hbound := (K.pullback f).oneMeetLevel_le_min x y
      omega
    · exact (hone x y hx hy).symm
  · intro a b c d ha hb hc hd hab hcd
    obtain ⟨x₀, hx₀, rfl⟩ := ha
    obtain ⟨x₁, hx₁, rfl⟩ := hb
    obtain ⟨y₀, hy₀, rfl⟩ := hc
    obtain ⟨y₁, hy₁, rfl⟩ := hd
    have hxx : x₀ < x₁ := by
      by_contra hn
      have hle : x₁ ≤ x₀ := Nat.le_of_not_gt hn
      exact (not_le_of_gt hab) (hf.monotone hle)
    have hyy : y₀ < y₁ := by
      by_contra hn
      have hle : y₁ ≤ y₀ := Nat.le_of_not_gt hn
      exact (not_le_of_gt hcd) (hf.monotone hle)
    refine ⟨(K.pullback f).twoMeetLevel x₀ x₁ y₀ y₁, ?_, ?_⟩
    · have hbound :=
        (K.pullback f).twoMeetLevel_le_min x₀ x₁ y₀ y₁
      omega
    · exact (K.selected_full_twoMeet_preserved f hf limit hone haux
        x₀ x₁ y₀ y₁ hxx hyy hx₁ hy₁).symm

end Ordered3Graph
end ThreeUniformDiaries
