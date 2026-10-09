import ThreeUniformDiaries.CanonicalAgreement
import ThreeUniformDiaries.ExactTypeMeetLevels

/-!
# Exact capped meets under canonical maps on the three type trees

The canonical-map lemma compares types at the selected level values.
Agreement at the selected cut and preservation of the first witness
at that cut imply equality of the *literal* capped meet values.
This does not assume that the selected levels are consecutive.

The finite vertex bounds matter: the canonical map of an EnumNode N
is compared only on vertices in N.
-/

namespace ThreeUniformDiaries
namespace CanonicalMap

/-- A canonical map preserves the literal singleton meet of all
vertices belonging to its finite input enumeration. -/
theorem oneMeetLevel_preserved_on_finite
    (F : CanonicalMap) {N : Nat} (H : EnumNode N)
    (u v : Nat) (hu : u < N) (hv : v < N) :
    (F.mapEnum N H).toOrdered3Graph.oneMeetLevel
      (F.level u) (F.level v) =
      F.level (H.toOrdered3Graph.oneMeetLevel u v) := by
  classical
  let src := H.toOrdered3Graph
  let dst := (F.mapEnum N H).toOrdered3Graph
  let w := src.oneMeetLevel u v
  have hwbound : w ≤ min u v := src.oneMeetLevel_le_min u v
  have hwu : w ≤ u := hwbound.trans (min_le_left _ _)
  have hwv : w ≤ v := hwbound.trans (min_le_right _ _)
  have hsource : src.SameOneTypeBelow w u v :=
    src.oneMeetLevel_agree u v
  have htarget : dst.SameOneTypeBelow
      (F.level w) (F.level u) (F.level v) :=
    (F.preserves_selected_one_agreement H hwu hwv hu hv).mp hsource
  have htargetBound :
      F.level w ≤ min (F.level u) (F.level v) :=
    le_min (F.strictMono.monotone hwu) (F.strictMono.monotone hwv)
  have hlow : F.level w ≤
      dst.oneMeetLevel (F.level u) (F.level v) :=
    Nat.le_findGreatest htargetBound htarget
  have hupper : dst.oneMeetLevel (F.level u) (F.level v) ≤
      min (F.level u) (F.level v) :=
    dst.oneMeetLevel_le_min (F.level u) (F.level v)
  by_cases hcap : w = min u v
  · have hmin : min (F.level u) (F.level v) =
        F.level (min u v) := by
      rcases le_total u v with huv | hvu
      · simp [min_eq_left huv, min_eq_left (F.strictMono.monotone huv)]
      · simp [min_eq_right hvu, min_eq_right (F.strictMono.monotone hvu)]
    have hhigh :
        dst.oneMeetLevel (F.level u) (F.level v) ≤ F.level w := by
      rw [hcap, ← hmin]
      exact hupper
    exact Nat.le_antisymm hhigh hlow
  · have hwlt : w < min u v := by omega
    have hfail : ¬ src.SameOneTypeBelow (w + 1) u v := by
      intro hnext
      have hwplus : w + 1 ≤ min u v := by omega
      have hh : w + 1 ≤ src.oneMeetLevel u v :=
        Nat.le_findGreatest hwplus hnext
      omega
    have hnew : ¬ ∀ a : Nat, a < w →
        (src.edge a w u ↔ src.edge a w v) := by
      intro hn
      exact hfail ((src.sameOneTypeBelow_succ_iff w u v).mpr ⟨hsource, hn⟩)
    push_neg at hnew
    rcases hnew with ⟨a, haw, hdiff⟩
    have htargetFail :
        ¬ dst.SameOneTypeBelow (F.level w + 1) (F.level u) (F.level v) := by
      intro ht
      have hwul : w < u := by omega
      have hwvl : w < v := by omega
      have htbit := ht (F.strictMono haw)
        (by omega : F.level w < F.level w + 1)
      have hl := F.preserves_selected_edges H haw hwul hu
      have hr := F.preserves_selected_edges H haw hwvl hv
      have heq := hl.trans (htbit.trans hr.symm)
      rcases hdiff with h | h
      · exact h.2 (heq.mp h.1)
      · exact h.1 (heq.mpr h.2)
    have htop :
        dst.oneMeetLevel (F.level u) (F.level v) < F.level w + 1 := by
      by_contra hn
      have hcut :
          F.level w + 1 ≤ dst.oneMeetLevel (F.level u) (F.level v) :=
        Nat.le_of_not_gt hn
      have hall := dst.oneMeetLevel_agree (F.level u) (F.level v)
      have hbad : dst.SameOneTypeBelow (F.level w + 1)
          (F.level u) (F.level v) := by
        intro a b hab hb
        exact hall hab (lt_of_lt_of_le hb hcut)
      exact htargetFail hbad
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp htop) hlow

/-- A canonical map also preserves the exact capped auxiliary meet
for increasing pairs of vertices in its finite input enumeration. -/
theorem auxMeetLevel_preserved_on_finite
    (F : CanonicalMap) {N : Nat} (H : EnumNode N)
    (u₀ u₁ v₀ v₁ : Nat) (hu : u₀ < u₁) (huN : u₁ < N)
    (hv : v₀ < v₁) (hvN : v₁ < N) :
    (F.mapEnum N H).toOrdered3Graph.auxMeetLevel
      (F.level u₀) (F.level u₁) (F.level v₀) (F.level v₁) =
      F.level (H.toOrdered3Graph.auxMeetLevel u₀ u₁ v₀ v₁) := by
  classical
  let src := H.toOrdered3Graph
  let dst := (F.mapEnum N H).toOrdered3Graph
  let w := src.auxMeetLevel u₀ u₁ v₀ v₁
  have hwbound : w ≤ min u₀ v₀ :=
    src.auxMeetLevel_le_min u₀ u₁ v₀ v₁
  have hwu : w ≤ u₀ := hwbound.trans (min_le_left _ _)
  have hwv : w ≤ v₀ := hwbound.trans (min_le_right _ _)
  have hsource : src.SameAuxTypeBelow w u₀ u₁ v₀ v₁ :=
    src.auxMeetLevel_agree u₀ u₁ v₀ v₁
  have htarget : dst.SameAuxTypeBelow
      (F.level w) (F.level u₀) (F.level u₁)
      (F.level v₀) (F.level v₁) :=
    (F.preserves_selected_aux_agreement H hwu hu huN hwv hv hvN).mp hsource
  have htargetBound :
      F.level w ≤ min (F.level u₀) (F.level v₀) :=
    le_min (F.strictMono.monotone hwu) (F.strictMono.monotone hwv)
  have hlow : F.level w ≤
      dst.auxMeetLevel (F.level u₀) (F.level u₁)
        (F.level v₀) (F.level v₁) :=
    Nat.le_findGreatest htargetBound htarget
  have hupper :
      dst.auxMeetLevel (F.level u₀) (F.level u₁)
        (F.level v₀) (F.level v₁) ≤
          min (F.level u₀) (F.level v₀) :=
    dst.auxMeetLevel_le_min
      (F.level u₀) (F.level u₁) (F.level v₀) (F.level v₁)
  by_cases hcap : w = min u₀ v₀
  · have hmin : min (F.level u₀) (F.level v₀) =
        F.level (min u₀ v₀) := by
      rcases le_total u₀ v₀ with huv | hvu
      · simp [min_eq_left huv, min_eq_left (F.strictMono.monotone huv)]
      · simp [min_eq_right hvu, min_eq_right (F.strictMono.monotone hvu)]
    have hhigh :
        dst.auxMeetLevel (F.level u₀) (F.level u₁)
          (F.level v₀) (F.level v₁) ≤ F.level w := by
      rw [hcap, ← hmin]
      exact hupper
    exact Nat.le_antisymm hhigh hlow
  · have hwlt : w < min u₀ v₀ := by omega
    have hfail :
        ¬ src.SameAuxTypeBelow (w + 1) u₀ u₁ v₀ v₁ := by
      intro hnext
      have hwplus : w + 1 ≤ min u₀ v₀ := by omega
      have hh : w + 1 ≤ src.auxMeetLevel u₀ u₁ v₀ v₁ :=
        Nat.le_findGreatest hwplus hnext
      omega
    have hdiff :
        ¬ (src.edge w u₀ u₁ ↔ src.edge w v₀ v₁) := by
      intro heq
      exact hfail
        ((src.sameAuxTypeBelow_succ_iff w u₀ u₁ v₀ v₁).mpr
          ⟨hsource, heq⟩)
    have htargetFail :
        ¬ dst.SameAuxTypeBelow (F.level w + 1)
          (F.level u₀) (F.level u₁) (F.level v₀) (F.level v₁) := by
      intro ht
      have hwul : w < u₀ := by omega
      have hwvl : w < v₀ := by omega
      have htbit := ht (by omega : F.level w < F.level w + 1)
      have hl := F.preserves_selected_edges H hwul hu huN
      have hr := F.preserves_selected_edges H hwvl hv hvN
      exact hdiff (hl.trans (htbit.trans hr.symm))
    have htop :
        dst.auxMeetLevel (F.level u₀) (F.level u₁)
          (F.level v₀) (F.level v₁) < F.level w + 1 := by
      by_contra hn
      have hcut :
          F.level w + 1 ≤
            dst.auxMeetLevel (F.level u₀) (F.level u₁)
              (F.level v₀) (F.level v₁) := Nat.le_of_not_gt hn
      have hall := dst.auxMeetLevel_agree
        (F.level u₀) (F.level u₁) (F.level v₀) (F.level v₁)
      have hbad : dst.SameAuxTypeBelow (F.level w + 1)
          (F.level u₀) (F.level u₁) (F.level v₀) (F.level v₁) := by
        intro a ha
        exact hall (lt_of_lt_of_le ha hcut)
      exact htargetFail hbad
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp htop) hlow

end CanonicalMap
end ThreeUniformDiaries
