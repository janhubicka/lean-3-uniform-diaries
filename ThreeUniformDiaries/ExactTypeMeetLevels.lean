import ThreeUniformDiaries.TypeCutTransfer
import Mathlib.Data.Nat.Find

/-!
# Exact singleton and auxiliary meets from selected-cut comparisons

The manuscript defines the meet of singleton (respectively auxiliary)
types as the last level at which they agree, capped by the smaller
source vertex (respectively smaller minimum of the two pairs).

The earlier transfer lemmas check agreement at selected cuts and
preserve the first disagreement at the selected image of that cut.
This file assembles these two ingredients to prove *literal equality
of meet levels* in the source and target. It does not assume convexity
of the target image, nor that the selected image levels are consecutive.

The source/target gap hypotheses here are explicit. The concrete
K_I construction will supply them by inherited-gap propagation.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Last singleton-type agreement cut, capped at the smaller vertex. -/
noncomputable def oneMeetLevel (H : Ordered3Graph Nat)
    (u v : Nat) : Nat := by
  classical
  exact Nat.findGreatest (fun l => H.SameOneTypeBelow l u v) (min u v)

/-- Last auxiliary-type agreement cut, capped at the smaller pair minimum. -/
noncomputable def auxMeetLevel (H : Ordered3Graph Nat)
    (u₀ u₁ v₀ v₁ : Nat) : Nat := by
  classical
  exact Nat.findGreatest
    (fun l => H.SameAuxTypeBelow l u₀ u₁ v₀ v₁) (min u₀ v₀)

theorem oneMeetLevel_le_min (H : Ordered3Graph Nat) (u v : Nat) :
    H.oneMeetLevel u v ≤ min u v := by
  classical
  exact Nat.findGreatest_le (P := fun l => H.SameOneTypeBelow l u v) (min u v)

theorem auxMeetLevel_le_min (H : Ordered3Graph Nat)
    (u₀ u₁ v₀ v₁ : Nat) :
    H.auxMeetLevel u₀ u₁ v₀ v₁ ≤ min u₀ v₀ := by
  classical
  exact Nat.findGreatest_le
    (P := fun l => H.SameAuxTypeBelow l u₀ u₁ v₀ v₁) (min u₀ v₀)

theorem oneMeetLevel_agree (H : Ordered3Graph Nat) (u v : Nat) :
    H.SameOneTypeBelow (H.oneMeetLevel u v) u v := by
  classical
  unfold oneMeetLevel
  apply Nat.findGreatest_spec
    (P := fun l => H.SameOneTypeBelow l u v) (m := 0) (n := min u v)
  · omega
  · intro a b hab hb
    omega

theorem auxMeetLevel_agree (H : Ordered3Graph Nat)
    (u₀ u₁ v₀ v₁ : Nat) :
    H.SameAuxTypeBelow (H.auxMeetLevel u₀ u₁ v₀ v₁)
      u₀ u₁ v₀ v₁ := by
  classical
  unfold auxMeetLevel
  apply Nat.findGreatest_spec
    (P := fun l => H.SameAuxTypeBelow l u₀ u₁ v₀ v₁)
    (m := 0) (n := min u₀ v₀)
  · omega
  · intro a ha
    omega

/-- The exact singleton-type meet is preserved whenever the
selected/omitted pair comparison is valid at source agreement cuts. -/
theorem oneMeetLevel_preserved
    (H G : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (hedge : ∀ a b c : Nat, a < b → b < c →
      (H.edge a b c ↔ G.edge (f a) (f b) (f c)))
    (hgap : ∀ w u v : Nat, w ≤ u → w ≤ v →
      H.SameOneTypeBelow w u v →
      ∀ x y : Nat, x < y → y < f w →
        ((¬ ∃ a : Nat, f a = x) ∨ (¬ ∃ b : Nat, f b = y)) →
        (G.edge x y (f u) ↔ G.edge x y (f v)))
    (u v : Nat) :
    G.oneMeetLevel (f u) (f v) = f (H.oneMeetLevel u v) := by
  classical
  let w := H.oneMeetLevel u v
  have hbound : w ≤ min u v := H.oneMeetLevel_le_min u v
  have hwu : w ≤ u := hbound.trans (min_le_left _ _)
  have hwv : w ≤ v := hbound.trans (min_le_right _ _)
  have hagree : H.SameOneTypeBelow w u v := H.oneMeetLevel_agree u v
  have htarget : G.SameOneTypeBelow (f w) (f u) (f v) :=
    oneTypeAgreement_transfer H G f hf hedge w u v
      hwu hwv hagree (hgap w u v hwu hwv hagree)
  have htargetBound : f w ≤ min (f u) (f v) :=
    le_min (hf.monotone hwu) (hf.monotone hwv)
  have hlow : f w ≤ G.oneMeetLevel (f u) (f v) := by
    exact Nat.le_findGreatest htargetBound htarget
  have hupper : G.oneMeetLevel (f u) (f v) ≤ min (f u) (f v) :=
    G.oneMeetLevel_le_min (f u) (f v)
  by_cases hcap : w = min u v
  · have hmin : min (f u) (f v) = f (min u v) := by
      rcases le_total u v with huv | hvu
      · simp [min_eq_left huv, min_eq_left (hf.monotone huv)]
      · simp [min_eq_right hvu, min_eq_right (hf.monotone hvu)]
    have hhigh : G.oneMeetLevel (f u) (f v) ≤ f w := by
      rw [hcap, ← hmin]
      exact hupper
    exact Nat.le_antisymm hhigh hlow
  · have hwlt : w < min u v := by omega
    have hfail : ¬ H.SameOneTypeBelow (w + 1) u v := by
      intro hnext
      have hwplus : w + 1 ≤ min u v := by omega
      have hh : w + 1 ≤ H.oneMeetLevel u v :=
        Nat.le_findGreatest hwplus hnext
      omega
    have htargetFail :
        ¬ G.SameOneTypeBelow (f w + 1) (f u) (f v) :=
      oneType_failure_at_image_cut H G f hf hedge
        w u v (by omega) (by omega) hagree hfail
    have htop : G.oneMeetLevel (f u) (f v) < f w + 1 := by
      by_contra hn
      have hcut : f w + 1 ≤ G.oneMeetLevel (f u) (f v) :=
        Nat.le_of_not_gt hn
      have hall := G.oneMeetLevel_agree (f u) (f v)
      have hbad : G.SameOneTypeBelow (f w + 1) (f u) (f v) := by
        intro a b hab hb
        exact hall hab (lt_of_lt_of_le hb hcut)
      exact htargetFail hbad
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp htop) hlow

/-- The exact auxiliary-type meet is likewise preserved whenever
target vertices omitted from the image give zero auxiliary tests. -/
theorem auxMeetLevel_preserved
    (H G : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (hedge : ∀ a b c : Nat, a < b → b < c →
      (H.edge a b c ↔ G.edge (f a) (f b) (f c)))
    (hzero : ∀ w u₀ u₁ : Nat, w ≤ u₀ → u₀ < u₁ →
      ∀ x : Nat, x < f w →
        (¬ ∃ a : Nat, f a = x) →
        ¬ G.edge x (f u₀) (f u₁))
    (u₀ u₁ v₀ v₁ : Nat) (hu : u₀ < u₁) (hv : v₀ < v₁) :
    G.auxMeetLevel (f u₀) (f u₁) (f v₀) (f v₁) =
      f (H.auxMeetLevel u₀ u₁ v₀ v₁) := by
  classical
  let w := H.auxMeetLevel u₀ u₁ v₀ v₁
  have hbound : w ≤ min u₀ v₀ :=
    H.auxMeetLevel_le_min u₀ u₁ v₀ v₁
  have hwu : w ≤ u₀ := hbound.trans (min_le_left _ _)
  have hwv : w ≤ v₀ := hbound.trans (min_le_right _ _)
  have hagree : H.SameAuxTypeBelow w u₀ u₁ v₀ v₁ :=
    H.auxMeetLevel_agree u₀ u₁ v₀ v₁
  have htarget : G.SameAuxTypeBelow (f w)
      (f u₀) (f u₁) (f v₀) (f v₁) := by
    apply auxTypeAgreement_transfer H G f hf hedge
      w u₀ u₁ v₀ v₁ hwu hu hwv hv hagree
    intro x hx hmiss
    exact ⟨hzero w u₀ u₁ hwu hu x hx hmiss,
      hzero w v₀ v₁ hwv hv x hx hmiss⟩
  have htargetBound : f w ≤ min (f u₀) (f v₀) :=
    le_min (hf.monotone hwu) (hf.monotone hwv)
  have hlow : f w ≤ G.auxMeetLevel (f u₀) (f u₁) (f v₀) (f v₁) :=
    Nat.le_findGreatest htargetBound htarget
  have hupper : G.auxMeetLevel (f u₀) (f u₁) (f v₀) (f v₁) ≤
      min (f u₀) (f v₀) :=
    G.auxMeetLevel_le_min (f u₀) (f u₁) (f v₀) (f v₁)
  by_cases hcap : w = min u₀ v₀
  · have hmin : min (f u₀) (f v₀) = f (min u₀ v₀) := by
      rcases le_total u₀ v₀ with huv | hvu
      · simp [min_eq_left huv, min_eq_left (hf.monotone huv)]
      · simp [min_eq_right hvu, min_eq_right (hf.monotone hvu)]
    have hhigh : G.auxMeetLevel (f u₀) (f u₁) (f v₀) (f v₁) ≤ f w := by
      rw [hcap, ← hmin]
      exact hupper
    exact Nat.le_antisymm hhigh hlow
  · have hwlt : w < min u₀ v₀ := by omega
    have hfail : ¬ H.SameAuxTypeBelow (w + 1) u₀ u₁ v₀ v₁ := by
      intro hnext
      have hwplus : w + 1 ≤ min u₀ v₀ := by omega
      have hh : w + 1 ≤ H.auxMeetLevel u₀ u₁ v₀ v₁ :=
        Nat.le_findGreatest hwplus hnext
      omega
    have htargetFail :
        ¬ G.SameAuxTypeBelow (f w + 1) (f u₀) (f u₁)
          (f v₀) (f v₁) :=
      auxType_failure_at_image_cut H G f hf hedge
        w u₀ u₁ v₀ v₁ (by omega) hu (by omega) hv hfail hagree
    have htop :
        G.auxMeetLevel (f u₀) (f u₁) (f v₀) (f v₁) < f w + 1 := by
      by_contra hn
      have hcut :
          f w + 1 ≤ G.auxMeetLevel (f u₀) (f u₁) (f v₀) (f v₁) :=
        Nat.le_of_not_gt hn
      have hall := G.auxMeetLevel_agree
        (f u₀) (f u₁) (f v₀) (f v₁)
      have hbad :
          G.SameAuxTypeBelow (f w + 1)
            (f u₀) (f u₁) (f v₀) (f v₁) := by
        intro a ha
        exact hall (lt_of_lt_of_le ha hcut)
      exact htargetFail hbad
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp htop) hlow

end Ordered3Graph
end ThreeUniformDiaries
