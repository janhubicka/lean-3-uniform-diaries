import ThreeUniformDiaries.DiarySingletonEnvelopeTransfer
import ThreeUniformDiaries.DiaryAuxEnvelopeTransfer

/-!
# ATR for the two-tail diary envelope

When the singleton meet of two leaves lies before the protected cut,
their pointed type envelope contains only the full prefix and the two
leaves. There is exactly one pair entirely outside that prefix,
so no additional auxiliary-disagreement hypothesis is needed.

This file verifies all singleton and auxiliary pair meets for the
canonical induced finite-carrier compression, even when selected
vertices skip arbitrary target levels.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- All auxiliary meets in a prefix-plus-two-tail induced carrier
are preserved: two distinct pairs wholly outside the prefix cannot
exist. -/
theorem two_tail_auxMeet_preserved
    (H : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (n : Nat) (hfix : ∀ z, z < n → f z = z)
    (a b c d : Nat) (hab : a < b) (hcd : c < d)
    (hb : b < n+2) (hd : d < n+2) :
    H.auxMeetLevel (f a) (f b) (f c) (f d) =
      f ((H.pullback f).auxMeetLevel a b c d) := by
  apply H.pullback_auxMeetLevel_preserved_of_early_distinctions
    f hf n (n+2) hfix
  · intro u₀ u₁ v₀ v₁ hu hv huBound hvBound hnu hnv hne
    have h0 : u₀ = n := by omega
    have h1 : u₁ = n+1 := by omega
    have h2 : v₀ = n := by omega
    have h3 : v₁ = n+1 := by omega
    exact (hne (by simp only [h0,h1,h2,h3])).elim
  · exact hab
  · exact hcd
  · exact hb
  · exact hd

/-- If the two exterior leaves have singleton meet before the
protected cut, all singleton meets of the selected finite carrier
are preserved exactly by the induced enumeration. -/
theorem two_tail_oneMeet_preserved
    (H : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (n : Nat) (hfix : ∀ z, z < n → f z = z)
    (htail : H.oneMeetLevel (f n) (f (n+1)) < n)
    (u v : Nat) (hu : u < n+2) (hv : v < n+2) :
    H.oneMeetLevel (f u) (f v) =
      f ((H.pullback f).oneMeetLevel u v) := by
  classical
  by_cases heq : u = v
  · subst v
    simp only [oneMeetLevel_self_full]
  · have hearly : H.oneMeetLevel (f u) (f v) < n := by
      by_cases hprefix : min u v < n
      · have hmin : min (f u) (f v) = f (min u v) := by
          rcases le_total u v with huv | hvu
          · simp [min_eq_left huv, min_eq_left (hf.monotone huv)]
          · simp [min_eq_right hvu, min_eq_right (hf.monotone hvu)]
        have hbound : H.oneMeetLevel (f u) (f v) ≤ f (min u v) := by
          rw [← hmin]
          exact H.oneMeetLevel_le_min (f u) (f v)
        rw [hfix (min u v) hprefix] at hbound
        omega
      · have hnu : n ≤ u := by omega
        have hnv : n ≤ v := by omega
        rcases lt_trichotomy u v with huv | huv | hvu
        · have huN : u = n := by omega
          have hvN : v = n+1 := by omega
          simpa only [huN,hvN] using htail
        · exact (heq huv).elim
        · have huN : u = n+1 := by omega
          have hvN : v = n := by omega
          have hcomm := H.oneMeetLevel_comm (f (n+1)) (f n)
          rw [huN,hvN, hcomm]
          exact htail
    have hsrc := H.pullback_oneMeetLevel_of_lt_prefix f hf n u v
      hfix hearly
    have hsrcLt : (H.pullback f).oneMeetLevel u v < n := by
      rw [hsrc]
      exact hearly
    calc
      H.oneMeetLevel (f u) (f v) =
        (H.pullback f).oneMeetLevel u v := hsrc.symm
      _ = f ((H.pullback f).oneMeetLevel u v) :=
        (hfix _ hsrcLt).symm

/-- Complete ATR on the selected prefix-plus-two-vertex carrier.
Only the early leaf singleton meet is required. -/
theorem pointed_two_tail_ATR_finite
    (H : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (n : Nat) (hfix : ∀ z, z < n → f z = z)
    (htail : H.oneMeetLevel (f n) (f (n+1)) < n) :
    (∀ u v, u < n+2 → v < n+2 →
      H.oneMeetLevel (f u) (f v) =
        f ((H.pullback f).oneMeetLevel u v)) ∧
    (∀ a b c d, a < b → c < d →
      b < n+2 → d < n+2 →
      H.auxMeetLevel (f a) (f b) (f c) (f d) =
        f ((H.pullback f).auxMeetLevel a b c d)) := by
  constructor
  · intro u v hu hv
    exact H.two_tail_oneMeet_preserved f hf n hfix htail u v hu hv
  · intro a b c d hab hcd hb hd
    exact H.two_tail_auxMeet_preserved f hf n hfix a b c d hab hcd hb hd

end Ordered3Graph
end ThreeUniformDiaries
