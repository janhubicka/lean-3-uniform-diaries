import ThreeUniformDiaries.DiaryPrefixCompression

/-!
# Singleton meets in pointed diary envelope compressions

The ATR-admissible envelope is obtained by retaining a full prefix
and two or three extra vertices. Type meets which split *within*
the fixed prefix are preserved automatically. The only late
singleton meet, between the two leaves, is reproduced by the
explicit marker-edge disagreement at their recorded 1-split.

This module proves both facts using actual edge-defined singleton
types; it never assumes that omitted target vertices are zero.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

private theorem mono_min_one (f : Nat → Nat) (hf : StrictMono f)
    (a b : Nat) : min (f a) (f b) = f (min a b) := by
  rcases le_total a b with hab | hba
  · simp [min_eq_left hab, min_eq_left (hf.monotone hab)]
  · simp [min_eq_right hba, min_eq_right (hf.monotone hba)]

private theorem mono_nat_ge_one (f : Nat → Nat) (hf : StrictMono f) :
    ∀ x, x ≤ f x := by
  intro x
  induction x with
  | zero => omega
  | succ x ih =>
    have h : f x + 1 ≤ f (Nat.succ x) :=
      Nat.succ_le_of_lt (hf (Nat.lt_succ_self x))
    exact le_trans (Nat.succ_le_succ ih) h

/-- Agreement of singleton types below a protected prefix is literally
the same in an induced compression as in the original graph. -/
theorem pullback_sameOneTypeBelow_iff
    (H : Ordered3Graph Nat) (f : Nat → Nat) (n k : Nat)
    (hfix : ∀ z, z < n → f z = z)
    (hk : k ≤ n) (u v : Nat) :
    (H.pullback f).SameOneTypeBelow k u v ↔
      H.SameOneTypeBelow k (f u) (f v) := by
  constructor
  · intro h x y hxy hy
    have hfx := hfix x (lt_trans hxy (lt_of_lt_of_le hy hk))
    have hfy := hfix y (lt_of_lt_of_le hy hk)
    simpa only [pullback, hfx, hfy] using
      (h (a := x) (b := y) hxy hy)
  · intro h x y hxy hy
    have hfx := hfix x (lt_trans hxy (lt_of_lt_of_le hy hk))
    have hfy := hfix y (lt_of_lt_of_le hy hk)
    simpa only [pullback, hfx, hfy] using
      (h (a := x) (b := y) hxy hy)

/-- Every singleton meet occurring strictly before a fixed prefix
survives induced compression, with no further omitted-gap condition. -/
theorem pullback_oneMeetLevel_of_lt_prefix
    (H : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (n u v : Nat)
    (hfix : ∀ z, z < n → f z = z)
    (hbefore : H.oneMeetLevel (f u) (f v) < n) :
    (H.pullback f).oneMeetLevel u v =
      H.oneMeetLevel (f u) (f v) := by
  classical
  let w := H.oneMeetLevel (f u) (f v)
  let cap := min u v
  have hmin : min (f u) (f v) = f cap :=
    mono_min_one f hf u v
  have htargetBound : w ≤ f cap := by
    simpa only [hmin] using H.oneMeetLevel_le_min (f u) (f v)
  have hcap : w ≤ cap := by
    by_contra hn
    have hcaplt : cap < w := by omega
    have hfixCap : f cap = cap := hfix cap (by omega)
    omega
  have hagree : (H.pullback f).SameOneTypeBelow w u v :=
    (H.pullback_sameOneTypeBelow_iff f n w hfix (by omega) u v).mpr
      (H.oneMeetLevel_agree (f u) (f v))
  have hlow : w ≤ (H.pullback f).oneMeetLevel u v :=
    Nat.le_findGreatest hcap hagree
  have hupper : (H.pullback f).oneMeetLevel u v ≤ cap :=
    (H.pullback f).oneMeetLevel_le_min u v
  by_cases hc : w = cap
  · omega
  · have hplus : w + 1 ≤ cap := by omega
    have hplusN : w + 1 ≤ n := by omega
    by_contra hn
    have hgt : w < (H.pullback f).oneMeetLevel u v := by
      omega
    have hagreeNext : (H.pullback f).SameOneTypeBelow (w+1) u v := by
      intro x y hxy hy
      exact ((H.pullback f).oneMeetLevel_agree u v)
        hxy (lt_of_lt_of_le hy (by omega))
    have htargetNext := (H.pullback_sameOneTypeBelow_iff f n
      (w+1) hfix hplusN u v).mp hagreeNext
    have htargetCap : w + 1 ≤ min (f u) (f v) := by
      rw [hmin]
      exact hplus.trans (mono_nat_ge_one f hf cap)
    have hw : w + 1 ≤ H.oneMeetLevel (f u) (f v) := by
      exact Nat.le_findGreatest
        (P := fun k => H.SameOneTypeBelow k (f u) (f v))
        htargetCap htargetNext
    omega

/-- If the target singleton meet is capped at the image of the
smaller vertex, the pullback singleton meet is also capped. -/
theorem pullback_oneMeetLevel_of_target_cap
    (H : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (u v : Nat)
    (hcap : H.oneMeetLevel (f u) (f v) = f (min u v)) :
    (H.pullback f).oneMeetLevel u v = min u v := by
  classical
  let t := min u v
  have htarget : H.SameOneTypeBelow (f t) (f u) (f v) := by
    rw [← hcap]
    exact H.oneMeetLevel_agree (f u) (f v)
  have hsrc : (H.pullback f).SameOneTypeBelow t u v := by
    intro x y hxy hy
    exact htarget (hf hxy) (hf hy)
  have hlow : t ≤ (H.pullback f).oneMeetLevel u v :=
    Nat.le_findGreatest (by rfl) hsrc
  have hu := (H.pullback f).oneMeetLevel_le_min u v
  omega

/-- The special non-capped singleton meet in a three-tail-vertex
pointed envelope. The target has leaves e(n+1), e(n+2), whose
meet is e(n). A marker discrepancy at a retained prefix vertex
ensures that compression does not lose the first difference. -/
theorem pullback_oneMeetLevel_at_first_tail
    (H : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (n : Nat)
    (hmeet : H.oneMeetLevel (f (n+1)) (f (n+2)) = f n)
    (hwitness : ∃ z, z < n ∧
      ¬ (H.edge (f z) (f n) (f (n+1)) ↔
         H.edge (f z) (f n) (f (n+2)))) :
    (H.pullback f).oneMeetLevel (n+1) (n+2) = n := by
  classical
  let S := H.pullback f
  have htarget : H.SameOneTypeBelow (f n) (f (n+1)) (f (n+2)) := by
    rw [← hmeet]
    exact H.oneMeetLevel_agree (f (n+1)) (f (n+2))
  have hsrc : S.SameOneTypeBelow n (n+1) (n+2) := by
    intro x y hxy hyn
    exact htarget (hf hxy) (hf hyn)
  have hlow : n ≤ S.oneMeetLevel (n+1) (n+2) := by
    apply Nat.le_findGreatest (by omega)
    exact hsrc
  have hfail : ¬ S.SameOneTypeBelow (n+1) (n+1) (n+2) := by
    intro h
    obtain ⟨z, hzn, hdiff⟩ := hwitness
    have hb := h (a := z) (b := n) (by omega) (by omega)
    exact hdiff hb
  have hhigh : S.oneMeetLevel (n+1) (n+2) ≤ n := by
    by_contra hn
    have hnext : n + 1 ≤ S.oneMeetLevel (n+1) (n+2) := by
      omega
    have hnxtType : S.SameOneTypeBelow (n+1) (n+1) (n+2) := by
      intro x y hxy hy
      exact (S.oneMeetLevel_agree (n+1) (n+2))
        hxy (lt_of_lt_of_le hy hnext)
    exact hfail hnxtType
  exact Nat.le_antisymm hhigh hlow

end Ordered3Graph
end ThreeUniformDiaries
