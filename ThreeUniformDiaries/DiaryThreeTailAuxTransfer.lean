import ThreeUniformDiaries.DiaryThreeTailMarkerTable
import ThreeUniformDiaries.DiaryAuxEnvelopeTransfer

/-!
# Full auxiliary-meet preservation for a pointed three-tail envelope

Diary marker witnesses in a *generic target* need not sit literally at
indices 0, 1, 2: the original diary may have been embedded with gaps.
Their images do, however, remain below the protected prefix n.

This module replaces the stronger and inapplicable fixed-index bound
`auxMeet ≤ 2` by the correct general bound `auxMeet < n`. It then
assembles the exhaustive three-pair table with the exact induced
compression theorem, covering *all* pair comparisons on the finite
pointed carrier, including prefix, mixed, diagonal and exterior pairs.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

private theorem classify_three_tail_pair_general
    (n a b : Nat) (ha : n ≤ a) (hab : a < b)
    (hb : b < n+3) :
    (a=n ∧ b=n+1) ∨
      (a=n ∧ b=n+2) ∨
      (a=n+1 ∧ b=n+2) := by
  omega

/-- The three marked exterior disagreements may be witnessed at any
three vertices strictly below the protected prefix, not just 0,1,2. -/
theorem three_tail_distinct_aux_meet_lt_prefix_general
    (H : Ordered3Graph Nat) (f : Nat → Nat)
    (n : Nat)
    (h01 : H.auxMeetLevel
      (f n) (f (n+1)) (f n) (f (n+2)) < n)
    (h02 : H.auxMeetLevel
      (f n) (f (n+1)) (f (n+1)) (f (n+2)) < n)
    (h12 : H.auxMeetLevel
      (f n) (f (n+2)) (f (n+1)) (f (n+2)) < n)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (hb : b < n+3) (hd : d < n+3)
    (ha : n ≤ a) (hc : n ≤ c)
    (hne : (a,b) ≠ (c,d)) :
    H.auxMeetLevel (f a) (f b) (f c) (f d) < n := by
  have h10 : H.auxMeetLevel
      (f n) (f (n+2)) (f n) (f (n+1)) < n := by
    rw [H.auxMeetLevel_comm (f n) (f (n+2)) (f n) (f (n+1))]
    exact h01
  have h20 : H.auxMeetLevel
      (f (n+1)) (f (n+2)) (f n) (f (n+1)) < n := by
    rw [H.auxMeetLevel_comm (f (n+1)) (f (n+2)) (f n) (f (n+1))]
    exact h02
  have h21 : H.auxMeetLevel
      (f (n+1)) (f (n+2)) (f n) (f (n+2)) < n := by
    rw [H.auxMeetLevel_comm (f (n+1)) (f (n+2)) (f n) (f (n+2))]
    exact h12
  rcases classify_three_tail_pair_general n a b ha hab hb with hAB | hAB | hAB
  · rcases hAB with ⟨haEq, hbEq⟩
    subst a
    subst b
    rcases classify_three_tail_pair_general n c d hc hcd hd with hCD | hCD | hCD
    · rcases hCD with ⟨hcEq, hdEq⟩
      subst c
      subst d
      exact (hne rfl).elim
    · rcases hCD with ⟨hcEq, hdEq⟩
      subst c
      subst d
      omega
    · rcases hCD with ⟨hcEq, hdEq⟩
      subst c
      subst d
      omega
  · rcases hAB with ⟨haEq, hbEq⟩
    subst a
    subst b
    rcases classify_three_tail_pair_general n c d hc hcd hd with hCD | hCD | hCD
    · rcases hCD with ⟨hcEq, hdEq⟩
      subst c
      subst d
      omega
    · rcases hCD with ⟨hcEq, hdEq⟩
      subst c
      subst d
      exact (hne rfl).elim
    · rcases hCD with ⟨hcEq, hdEq⟩
      subst c
      subst d
      omega
  · rcases hAB with ⟨haEq, hbEq⟩
    subst a
    subst b
    rcases classify_three_tail_pair_general n c d hc hcd hd with hCD | hCD | hCD
    · rcases hCD with ⟨hcEq, hdEq⟩
      subst c
      subst d
      omega
    · rcases hCD with ⟨hcEq, hdEq⟩
      subst c
      subst d
      omega
    · rcases hCD with ⟨hcEq, hdEq⟩
      subst c
      subst d
      exact (hne rfl).elim


/-- The complete auxiliary-meet half of ATR for the induced
three-tail envelope whose selected carrier is the first n+3 vertices.
No convexity of the target image is assumed. -/
theorem three_tail_auxMeet_preserved
    (H : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (n : Nat) (hfix : ∀ z, z < n → f z = z)
    (h01 : H.auxMeetLevel
      (f n) (f (n+1)) (f n) (f (n+2)) < n)
    (h02 : H.auxMeetLevel
      (f n) (f (n+1)) (f (n+1)) (f (n+2)) < n)
    (h12 : H.auxMeetLevel
      (f n) (f (n+2)) (f (n+1)) (f (n+2)) < n)
    (a b c d : Nat) (hab : a < b) (hcd : c < d)
    (hb : b < n+3) (hd : d < n+3) :
    H.auxMeetLevel (f a) (f b) (f c) (f d) =
      f ((H.pullback f).auxMeetLevel a b c d) := by
  exact H.pullback_auxMeetLevel_preserved_of_early_distinctions
    f hf n (n+3) hfix
    (fun u₀ u₁ v₀ v₁ hu hv huN hvN hnu hnv hne =>
      H.three_tail_distinct_aux_meet_lt_prefix_general
        f n h01 h02 h12 u₀ u₁ v₀ v₁
        hu hv huN hvN hnu hnv hne)
    a b c d hab hcd hb hd

end Ordered3Graph
end ThreeUniformDiaries
