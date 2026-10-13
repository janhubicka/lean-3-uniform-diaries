import ThreeUniformDiaries.DiaryPrefixCompression

/-!
# A generic finite-envelope auxiliary-meet transfer rule

A prefix-preserving induced compression is automatically
aux-type-respecting when any two distinct post-prefix pairs have
an auxiliary meet strictly before the protected prefix.

The diary's pointed envelope has just one pair (two-tail case),
or three pairs (three-tail case). The already checked marker
witnesses will supply this finite 'early distinctions' hypothesis.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Self-comparisons of ordered pairs meet at their cap. -/
theorem auxMeetLevel_self (H : Ordered3Graph Nat) (a b : Nat) :
    H.auxMeetLevel a b a b = a := by
  classical
  have hupper : H.auxMeetLevel a b a b ≤ a := by
    simpa using H.auxMeetLevel_le_min a b a b
  have hagree : H.SameAuxTypeBelow a a b a b := by
    intro z hz
    rfl
  have hlower : a ≤ H.auxMeetLevel a b a b := by
    exact Nat.le_findGreatest
      (P := fun k => H.SameAuxTypeBelow k a b a b) (by simp) hagree
  omega

/-- All pair auxiliary meets are preserved by an induced compression
which fixes the prefix, provided every comparison of two different
fully external pairs splits already within that fixed prefix.

The finite bound limit prevents accidentally assuming a global
Ramsey property for pairs outside the selected envelope. This theorem
is useful even when the compression skips arbitrary
target levels between selected vertices. -/
theorem pullback_auxMeetLevel_preserved_of_early_distinctions
    (H : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (n limit : Nat) (hfix : ∀ z, z < n → f z = z)
    (houter : ∀ a b c d : Nat,
      a < b → c < d → b < limit → d < limit →
      n ≤ a → n ≤ c → (a, b) ≠ (c, d) →
      H.auxMeetLevel (f a) (f b) (f c) (f d) < n)
    (a b c d : Nat) (hab : a < b) (hcd : c < d)
    (hb : b < limit) (hd : d < limit) :
    H.auxMeetLevel (f a) (f b) (f c) (f d) =
      f ((H.pullback f).auxMeetLevel a b c d) := by
  classical
  by_cases hprefix : min a c < n
  · have hmin : min (f a) (f c) = f (min a c) := by
      rcases le_total a c with hac | hca
      · simp [min_eq_left hac, min_eq_left (hf.monotone hac)]
      · simp [min_eq_right hca, min_eq_right (hf.monotone hca)]
    have htarget : H.auxMeetLevel (f a) (f b) (f c) (f d) < n := by
      have hb := H.auxMeetLevel_le_min (f a) (f b) (f c) (f d)
      rw [hmin, hfix (min a c) hprefix] at hb
      omega
    have hsrc := H.pullback_auxMeetLevel_of_lt_prefix f hf n a b c d
      hfix htarget
    have hcap := (H.pullback f).auxMeetLevel_le_min a b c d
    have hsrcLt : (H.pullback f).auxMeetLevel a b c d < n :=
      lt_of_le_of_lt hcap hprefix
    calc
      H.auxMeetLevel (f a) (f b) (f c) (f d) =
        (H.pullback f).auxMeetLevel a b c d := hsrc.symm
      _ = f ((H.pullback f).auxMeetLevel a b c d) :=
        (hfix _ hsrcLt).symm
  · have ha : n ≤ a := by omega
    have hc : n ≤ c := by omega
    by_cases heq : (a, b) = (c, d)
    · have hac : a = c := congrArg Prod.fst heq
      have hbd : b = d := congrArg Prod.snd heq
      subst c
      subst d
      simp only [auxMeetLevel_self]
    · have ht : H.auxMeetLevel (f a) (f b) (f c) (f d) < n :=
        houter a b c d hab hcd hb hd ha hc heq
      have hsrc := H.pullback_auxMeetLevel_of_lt_prefix
        f hf n a b c d hfix ht
      have hsrcLt : (H.pullback f).auxMeetLevel a b c d < n := by
        rw [hsrc]
        exact ht
      calc
        H.auxMeetLevel (f a) (f b) (f c) (f d) =
          (H.pullback f).auxMeetLevel a b c d := hsrc.symm
        _ = f ((H.pullback f).auxMeetLevel a b c d) :=
          (hfix _ hsrcLt).symm

end Ordered3Graph
end ThreeUniformDiaries
