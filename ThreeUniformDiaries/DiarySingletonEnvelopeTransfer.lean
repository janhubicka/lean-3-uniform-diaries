import ThreeUniformDiaries.DiarySingletonCompression

/-!
# Exact singleton meets on a three-tail pointed diary envelope

All singleton pairs in a compressed envelope preserving the first n
vertices satisfy one of three cases: meet before n, a diagonal cap,
or the special non-capped meet of the two final leaves at the
retained 1-split. This is the full singleton half of ATR
admissibility for a pointed three-vertex envelope.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- A singleton type agrees with itself through its entire cap. -/
theorem oneMeetLevel_self_full (H : Ordered3Graph Nat) (u : Nat) :
    H.oneMeetLevel u u = u := by
  classical
  have hupper : H.oneMeetLevel u u ≤ u := by
    simpa using H.oneMeetLevel_le_min u u
  have hagree : H.SameOneTypeBelow u u u := by
    intro x y hxy hy
    rfl
  have hlower : u ≤ H.oneMeetLevel u u := by
    exact Nat.le_findGreatest
      (P := fun k => H.SameOneTypeBelow k u u) (by simp) hagree
  omega

/-- Singleton-type meets are symmetric. -/
theorem oneMeetLevel_comm (H : Ordered3Graph Nat) (u v : Nat) :
    H.oneMeetLevel u v = H.oneMeetLevel v u := by
  classical
  have hab := H.oneMeetLevel_le_min u v
  have hba := H.oneMeetLevel_le_min v u
  have hagreeAB := H.oneMeetLevel_agree u v
  have hagreeBA := H.oneMeetLevel_agree v u
  have hleft : H.oneMeetLevel u v ≤ H.oneMeetLevel v u := by
    have hb : H.oneMeetLevel u v ≤ min v u := by
      simpa only [min_comm] using hab
    have ht : H.SameOneTypeBelow (H.oneMeetLevel u v) v u := by
      intro x y hxy hy
      exact (hagreeAB hxy hy).symm
    exact Nat.le_findGreatest
      (P := fun k => H.SameOneTypeBelow k v u) hb ht
  have hright : H.oneMeetLevel v u ≤ H.oneMeetLevel u v := by
    have hb : H.oneMeetLevel v u ≤ min u v := by
      simpa only [min_comm] using hba
    have ht : H.SameOneTypeBelow (H.oneMeetLevel v u) u v := by
      intro x y hxy hy
      exact (hagreeBA hxy hy).symm
    exact Nat.le_findGreatest
      (P := fun k => H.SameOneTypeBelow k u v) hb ht
  exact Nat.le_antisymm hleft hright

private theorem early_one_meet_preserved
    (H : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (n u v : Nat)
    (hfix : ∀ z, z < n → f z = z)
    (hearly : H.oneMeetLevel (f u) (f v) < n) :
    H.oneMeetLevel (f u) (f v) =
      f ((H.pullback f).oneMeetLevel u v) := by
  have heq := H.pullback_oneMeetLevel_of_lt_prefix f hf n u v hfix hearly
  have hsrc_lt : (H.pullback f).oneMeetLevel u v < n := by
    rw [heq]
    exact hearly
  calc
    H.oneMeetLevel (f u) (f v) =
      (H.pullback f).oneMeetLevel u v := heq.symm
    _ = f ((H.pullback f).oneMeetLevel u v) :=
      (hfix _ hsrc_lt).symm

private theorem classify_three_tail_singletons
    (n u v : Nat) (hu : n ≤ u) (huv : u < v)
    (hv : v < n+3) :
    (u=n ∧ v=n+1) ∨
      (u=n ∧ v=n+2) ∨
      (u=n+1 ∧ v=n+2) := by
  omega

/-- All singleton-meet comparisons between vertices in the
first n+3 levels of a compressed envelope are exact, given
the two early mixed-leaf meets and the final retained split. -/
theorem three_tail_oneMeet_preserved_ordered
    (H : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (n : Nat) (hfix : ∀ z, z < n → f z = z)
    (hm_a : H.oneMeetLevel (f n) (f (n+1)) < n)
    (hm_b : H.oneMeetLevel (f n) (f (n+2)) < n)
    (hab : H.oneMeetLevel (f (n+1)) (f (n+2)) = f n)
    (hwitness : ∃ z, z < n ∧
      ¬ (H.edge (f z) (f n) (f (n+1)) ↔
         H.edge (f z) (f n) (f (n+2))))
    (u v : Nat) (huv : u ≤ v) (hv : v < n+3) :
    H.oneMeetLevel (f u) (f v) =
      f ((H.pullback f).oneMeetLevel u v) := by
  by_cases heq : u=v
  · subst v
    simp only [oneMeetLevel_self_full]
  · have hlt : u < v := lt_of_le_of_ne huv heq
    by_cases hprefix : u < n
    · have hfu : f u = u := hfix u hprefix
      have hBound : H.oneMeetLevel (f u) (f v) ≤ f u :=
        (H.oneMeetLevel_le_min (f u) (f v)).trans (min_le_left _ _)
      have hbefore : H.oneMeetLevel (f u) (f v) < n := by
        omega
      exact early_one_meet_preserved H f hf n u v hfix hbefore
    · have htail : n ≤ u := by omega
      rcases classify_three_tail_singletons n u v htail hlt hv
        with hpair | hpair | hpair
      · rcases hpair with ⟨hU,hV⟩
        subst u
        subst v
        exact early_one_meet_preserved H f hf n (n) (n+1) hfix hm_a
      · rcases hpair with ⟨hU,hV⟩
        subst u
        subst v
        exact early_one_meet_preserved H f hf n (n) (n+2) hfix hm_b
      · rcases hpair with ⟨hU,hV⟩
        subst u
        subst v
        have hs := H.pullback_oneMeetLevel_at_first_tail f hf n hab hwitness
        calc
          H.oneMeetLevel (f (n+1)) (f (n+2)) = f n := hab
          _ = f ((H.pullback f).oneMeetLevel (n+1) (n+2)) := by
            rw [hs]

/-- The unordered form, exactly the singleton-meet half of ATR
for all vertices of the selected finite pointed carrier. -/
theorem three_tail_oneMeet_preserved
    (H : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (n : Nat) (hfix : ∀ z, z < n → f z = z)
    (hm_a : H.oneMeetLevel (f n) (f (n+1)) < n)
    (hm_b : H.oneMeetLevel (f n) (f (n+2)) < n)
    (hab : H.oneMeetLevel (f (n+1)) (f (n+2)) = f n)
    (hwitness : ∃ z, z < n ∧
      ¬ (H.edge (f z) (f n) (f (n+1)) ↔
         H.edge (f z) (f n) (f (n+2))))
    (u v : Nat) (hu : u < n+3) (hv : v < n+3) :
    H.oneMeetLevel (f u) (f v) =
      f ((H.pullback f).oneMeetLevel u v) := by
  rcases le_total u v with huv | hvu
  · exact H.three_tail_oneMeet_preserved_ordered f hf n
      hfix hm_a hm_b hab hwitness u v huv hv
  · have hrev := H.three_tail_oneMeet_preserved_ordered f hf n
      hfix hm_a hm_b hab hwitness v u hvu hu
    calc
      H.oneMeetLevel (f u) (f v) =
        H.oneMeetLevel (f v) (f u) := H.oneMeetLevel_comm (f u) (f v)
      _ = f ((H.pullback f).oneMeetLevel v u) := hrev
      _ = f ((H.pullback f).oneMeetLevel u v) := by
        rw [(H.pullback f).oneMeetLevel_comm v u]

end Ordered3Graph
end ThreeUniformDiaries
