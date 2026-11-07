import ThreeUniformDiaries.DiaryFullNewGeneratorProfileStabilisation
import ThreeUniformDiaries.DiaryPersistentLeafEscapeDichotomy

/-!
# Fixed full split profile: persistent next leaf or escape

For every finitely persistent old diary stage at a genuine source leaf,
the existing finite record theorem produces ONE complete new nonleaf
generator profile occurring at every finite horizon.

The remaining issue is not to stabilize one or two meets separately:
it is whether a single image of the new SOURCE LEAF can realize that
fixed full split profile at every horizon.

Here we prove a sharp dichotomy FOR ONE FIXED COMPLETE PROFILE:
either one compatible reserved next-leaf map is itself finitely
persistent, with exactly that nonleaf record, or for every target
bound B there is a finite horizon at which ALL reserved realizations
of that particular profile have new leaf image > B.

Crucially, every such horizon has an actual compatible realization
of the fixed profile. There is no assumed coherent infinite branch,
no hypothetical finite cover, and no countable diary unavoidability.
The escape alternative remains open to eliminate geometrically.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A genuinely finite-horizon realization with the prescribed
entire new nonleaf-generator profile and old support fixed. -/
def HasFixedNonleafProfileHorizon
    (H K : Ordered3Graph Nat) (F f : Nat → Nat)
    (m : Nat)
    (p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat))
    (n : Nat) : Prop :=
  ∃ g : Nat → Nat,
    ReservedDiaryStage H K F (m + 1 + n) g ∧
    CofinalDiaryStageCompatible H m f g ∧
    (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
      g u.val = p u)

/-- The full nonleaf-generator profile has no horizon instability:
restriction of a later reserved map preserves every old and new
generator image (and the old support). -/
theorem fixedNonleafProfileHorizon_down
    (H K : Ordered3Graph Nat) (F f : Nat → Nat)
    (m : Nat)
    (p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat))
    (n k : Nat) (hkn : k ≤ n)
    (hn : HasFixedNonleafProfileHorizon H K F f m p n) :
    HasFixedNonleafProfileHorizon H K F f m p k := by
  obtain ⟨g, Q, hOld, hProfile⟩ := hn
  exact ⟨g, Q.restrict (by omega), hOld, hProfile⟩

/-- Fix a COMPLETE simultaneous new-nonleaf split record p.
Assuming an actual reserved realization at EVERY finite horizon,
either that record admits a genuine persistent next-leaf successor,
or its realizing new-leaf images must eventually escape beyond
every target bound B. Both alternatives keep the SAME profile p.

Unlike a raw finite compactness appeal, this uses a finite set of
possible next-leaf images only in the bounded branch. -/
theorem fixedNonleafProfile_persistent_successor_or_escape
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat))
    (hProfile : ∀ n : Nat,
      HasFixedNonleafProfileHorizon H K F f m p n) :
    (∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g ∧
      (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
        g u.val = p u)) ∨
    (∀ B : Nat, ∃ n : Nat,
      HasFixedNonleafProfileHorizon H K F f m p n ∧
      (∀ g : Nat → Nat,
        ReservedDiaryStage H K F (m + 1 + n) g →
        CofinalDiaryStageCompatible H m f g →
        (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
          g u.val = p u) →
        B < g m)) := by
  classical
  by_cases hSucc :
      ∃ g : Nat → Nat,
        PersistentReservedDiaryStage H K F (m + 1) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
          g u.val = p u)
  · exact Or.inl hSucc
  · right
    intro B
    have hEscape :
        ∃ n : Nat, ∀ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g →
          CofinalDiaryStageCompatible H m f g →
          (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
            g u.val = p u) →
          B < g m := by
      by_contra hNone
      push_neg at hNone
      let T := {u : Nat // u ∈ newNonleafGeneratorSupport H m}
      let R : Nat → Nat → Prop := fun v n =>
        ∃ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g ∧
          CofinalDiaryStageCompatible H m f g ∧
          (∀ u : T, g u.val = p u) ∧
          g m = v
      have hDown : ∀ v n k : Nat, k ≤ n → R v n → R v k := by
        intro v n k hkn
        rintro ⟨g, Q, hOld, hP, hVal⟩
        exact ⟨g, Q.restrict (by omega), hOld, hP, hVal⟩
      have hBoundedCover :
          ∀ n : Nat, ∃ v : Nat,
            v ∈ Finset.range (B + 1) ∧ R v n := by
        intro n
        obtain ⟨g, Q, hOld, hP, hSmall⟩ := hNone n
        exact ⟨g m, Finset.mem_range.mpr (by omega),
          g, Q, hOld, hP, rfl⟩
      obtain ⟨v, _hv, hStable⟩ :=
        finite_choice_persistent_of_downward_type
          (Finset.range (B + 1)) R hDown hBoundedCover
      obtain ⟨g0, Q0, hOld0, hP0, hV0⟩ := hStable 0
      have hQ0 : ReservedDiaryStage H K F (m + 1) g0 := by
        simpa only [Nat.add_zero] using Q0
      have hPersistent :
          PersistentReservedDiaryStage H K F (m + 1) g0 := by
        refine ⟨hQ0, ?_⟩
        intro n
        obtain ⟨gN, QN, hOldN, hPN, hVN⟩ := hStable n
        have hQN0 : ReservedDiaryStage H K F (m + 1) gN :=
          QN.restrict (by omega)
        have hEqualLeaves :
            ∀ u : Nat, u ∈ countableDiaryLeafPrefix H (m + 1) →
              g0 u = gN u := by
          intro u hu
          rw [countableDiaryLeafPrefix_succ_of_leaf H m hm] at hu
          rcases Finset.mem_insert.mp hu with hUm | hOldLeaf
          · subst u
            exact hV0.trans hVN.symm
          · have huOld : u ∈ countableDiaryFiniteSupport H m :=
              mem_finiteLeafMeetSupport_leaf H
                (countableDiaryLeafPrefix H m) u hOldLeaf
            exact (hOld0 u huOld).trans (hOldN u huOld).symm
        have hSameSupport :=
          hQ0.1.eq_on_support_of_selected_leaves
            hQN0.1 hEqualLeaves
        refine ⟨gN, QN, ?_⟩
        intro u hu
        exact (hSameSupport u hu).symm
      exact hSucc ⟨g0, hPersistent, hOld0, hP0⟩
    obtain ⟨n, hEsc⟩ := hEscape
    exact ⟨n, hProfile n, hEsc⟩

/-- For every finitely persistent old leaf stage there is a
*single* full new-nonleaf record p realized at ALL horizons,
and relative to that very record the remaining obstruction is
EXACTLY persistence of the new leaf versus its escape to infinity.

The second alternative has genuine witnesses at each horizon.
It does not follow from finite-stage nonemptiness alone that the
first alternative must hold. -/
theorem persistent_stage_fixed_nonleaf_profile_dichotomy
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (P : PersistentReservedDiaryStage H K F m f) :
    ∃ p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat),
      (∀ n : Nat,
        HasFixedNonleafProfileHorizon H K F f m p n) ∧
      ((∃ g : Nat → Nat,
        PersistentReservedDiaryStage H K F (m + 1) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
          g u.val = p u)) ∨
      (∀ B : Nat, ∃ n : Nat,
        HasFixedNonleafProfileHorizon H K F f m p n ∧
        (∀ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g →
          CofinalDiaryStageCompatible H m f g →
          (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
            g u.val = p u) →
          B < g m))) := by
  obtain ⟨p, hAll⟩ :=
    persistent_stage_has_stable_new_nonleaf_record hm P
  refine ⟨p, ?_, ?_⟩
  · intro n
    obtain ⟨g, Q, hOld, hP⟩ := hAll n
    exact ⟨g, Q, hOld, hP⟩
  · exact fixedNonleafProfile_persistent_successor_or_escape
      hm p (by
        intro n
        obtain ⟨g, Q, hOld, hP⟩ := hAll n
        exact ⟨g, Q, hOld, hP⟩)

end DiaryLeafPriority
end ThreeUniformDiaries
