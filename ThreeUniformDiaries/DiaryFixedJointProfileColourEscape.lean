import ThreeUniformDiaries.DiaryUniformOldStageTailColour
import ThreeUniformDiaries.DiaryFixedFullSplitProfileEscape

/-!
# Track D: the exact next-leaf escape obstruction in ONE mixed type fibre

For a fixed old reserved support map f and a genuine new source leaf m,
the previous checked theorem produces ONE complete image record p of
all newly generated nonleaf splits AND ONE complete mixed singleton
colour c below the uniform old-stage cut. This *same pair (p,c)*
occurs in genuine old-compatible reserved maps at every finite horizon.

We prove the sharp remaining alternative inside this precise fibre:
either the pair (p,c) has a finitely persistent actual next-leaf image,
or for every numerical bound B there is a nonempty finite horizon at
which ALL (p,c)-realizations have new leaf images greater than B.

The proof uses finite-choice compactness ONLY with an explicit finite
set of next-leaf image values. It does not infer that recurrence of a
finite profile/colour alone gives a persistent leaf. No countable
diary unavoidability is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Existence of a genuine reserved finite-horizon realization
fixing the whole old support, every new nonleaf generator image
and one complete mixed singleton colour at the fixed old-stage cut. -/
def HasJointProfileColourHorizon
    (H K : Ordered3Graph Nat) (F f : Nat → Nat) (m : Nat)
    (p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat))
    (c : Fin (oldStageTailCut H m f) →
      Fin (oldStageTailCut H m f) → Bool)
    (n : Nat) : Prop :=
  ∃ g : Nat → Nat,
    ReservedDiaryStage H K F (m + 1 + n) g ∧
    CofinalDiaryStageCompatible H m f g ∧
    (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
      g u.val = p u) ∧
    DiaryLowerBoundColors.singletonColour K
      (oldStageTailCut H m f) (g m) = c

/-- A SINGLE finitely persistent reserved new-leaf successor in
the specified complete profile and complete mixed singleton type. -/
def HasPersistentNextLeafWithJointProfileColour
    (H K : Ordered3Graph Nat) (F f : Nat → Nat) (m : Nat)
    (p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat))
    (c : Fin (oldStageTailCut H m f) →
      Fin (oldStageTailCut H m f) → Bool) : Prop :=
  ∃ g : Nat → Nat,
    PersistentReservedDiaryStage H K F (m + 1) g ∧
    CofinalDiaryStageCompatible H m f g ∧
    (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
      g u.val = p u) ∧
    DiaryLowerBoundColors.singletonColour K
      (oldStageTailCut H m f) (g m) = c

/-- One numerical bound B works for some (p,c)-realization at
EACH horizon. The witnesses may differ with the horizon. -/
def HasUniformNextLeafBoundWithJointProfileColour
    (H K : Ordered3Graph Nat) (F f : Nat → Nat) (m : Nat)
    (p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat))
    (c : Fin (oldStageTailCut H m f) →
      Fin (oldStageTailCut H m f) → Bool) : Prop :=
  ∃ B : Nat, ∀ n : Nat, ∃ g : Nat → Nat,
    ReservedDiaryStage H K F (m + 1 + n) g ∧
    CofinalDiaryStageCompatible H m f g ∧
    (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
      g u.val = p u) ∧
    DiaryLowerBoundColors.singletonColour K
      (oldStageTailCut H m f) (g m) = c ∧
    g m ≤ B

/-- Restriction to an earlier horizon preserves the entire
profile, the colour, and old support compatibility. -/
theorem jointProfileColourHorizon_down
    (H K : Ordered3Graph Nat) (F f : Nat → Nat) (m : Nat)
    (p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat))
    (c : Fin (oldStageTailCut H m f) →
      Fin (oldStageTailCut H m f) → Bool)
    (n k : Nat) (hkn : k ≤ n)
    (h : HasJointProfileColourHorizon H K F f m p c n) :
    HasJointProfileColourHorizon H K F f m p c k := by
  obtain ⟨g, Q, hOld, hProfile, hColour⟩ := h
  exact ⟨g, Q.restrict (by omega), hOld, hProfile, hColour⟩

/-- Fixed full split profile AND full mixed old-cut colour:
the existence of one persistent next leaf is EQUIVALENT to a
uniform bound on some next-leaf image at every finite horizon.

In the reverse direction, two witnesses with identical old
supported images and identical new leaf images agree on the ENTIRE
new S1/S2-generated support, by the checked determinacy theorem.
The fixed colour condition is retained through the finite-choice
argument; it is NOT dropped in favour of another colour. -/
theorem persistent_jointProfileColour_iff_uniform_nextLeaf_bound
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat))
    (c : Fin (oldStageTailCut H m f) →
      Fin (oldStageTailCut H m f) → Bool) :
    HasPersistentNextLeafWithJointProfileColour H K F f m p c ↔
      HasUniformNextLeafBoundWithJointProfileColour H K F f m p c := by
  classical
  constructor
  · rintro ⟨g₀, P₀, hOld₀, hProfile₀, hColour₀⟩
    refine ⟨g₀ m, ?_⟩
    intro n
    obtain ⟨gN, QN, hCompatible⟩ := P₀.2 n
    have hOldN : CofinalDiaryStageCompatible H m f gN := by
      intro u hu
      have huNext : u ∈ countableDiaryFiniteSupport H (m + 1) :=
        countableDiaryFiniteSupport_mono H m (m + 1) (by omega) hu
      exact (hCompatible u huNext).trans (hOld₀ u hu)
    have hProfileN :
        ∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
          gN u.val = p u := by
      intro u
      have huNext : u.val ∈ countableDiaryFiniteSupport H (m + 1) :=
        ((mem_newNonleafGeneratorSupport_iff H m u.val).mp u.property).1
      exact (hCompatible u.val huNext).trans (hProfile₀ u)
    have hmNext : m ∈ countableDiaryFiniteSupport H (m + 1) := by
      exact mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H (m + 1)) m
        ((mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
          ⟨hm.1, by omega, hm⟩)
    have hColourN :
        DiaryLowerBoundColors.singletonColour K
          (oldStageTailCut H m f) (gN m) = c := by
      rw [hCompatible m hmNext]
      exact hColour₀
    refine ⟨gN, QN, hOldN, hProfileN, hColourN, ?_⟩
    rw [hCompatible m hmNext]
  · rintro ⟨B, hBound⟩
    let T := {u : Nat // u ∈ newNonleafGeneratorSupport H m}
    let R : Nat → Nat → Prop := fun v n =>
      ∃ g : Nat → Nat,
        ReservedDiaryStage H K F (m + 1 + n) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        (∀ u : T, g u.val = p u) ∧
        DiaryLowerBoundColors.singletonColour K
          (oldStageTailCut H m f) (g m) = c ∧
        g m = v
    have hDown : ∀ v n k : Nat, k ≤ n → R v n → R v k := by
      intro v n k hkn
      rintro ⟨g, Q, hOld, hProfile, hColour, hVal⟩
      exact ⟨g, Q.restrict (by omega), hOld, hProfile,
        hColour, hVal⟩
    have hCover : ∀ n : Nat, ∃ v : Nat,
        v ∈ Finset.range (B + 1) ∧ R v n := by
      intro n
      obtain ⟨g, Q, hOld, hProfile, hColour, hSmall⟩ := hBound n
      exact ⟨g m, Finset.mem_range.mpr (by omega),
        g, Q, hOld, hProfile, hColour, rfl⟩
    obtain ⟨v, _hv, hStable⟩ :=
      finite_choice_persistent_of_downward
        (Finset.range (B + 1)) R hDown hCover
    obtain ⟨g₀, Q₀, hOld₀, hProfile₀, hColour₀, hVal₀⟩ :=
      hStable 0
    have hQ₀ : ReservedDiaryStage H K F (m + 1) g₀ := by
      simpa only [Nat.add_zero] using Q₀
    have hPersistent :
        PersistentReservedDiaryStage H K F (m + 1) g₀ := by
      refine ⟨hQ₀, ?_⟩
      intro n
      obtain ⟨gN, QN, hOldN, _hProfileN, _hColourN, hValN⟩ :=
        hStable n
      have hQN₀ : ReservedDiaryStage H K F (m + 1) gN :=
        QN.restrict (by omega)
      have hEqualLeaves :
          ∀ u : Nat, u ∈ countableDiaryLeafPrefix H (m + 1) →
            g₀ u = gN u := by
        intro u hu
        rw [countableDiaryLeafPrefix_succ_of_leaf H m hm] at hu
        rcases Finset.mem_insert.mp hu with hUm | hOldLeaf
        · subst u
          exact hVal₀.trans hValN.symm
        · have huOld : u ∈ countableDiaryFiniteSupport H m :=
            mem_finiteLeafMeetSupport_leaf H
              (countableDiaryLeafPrefix H m) u hOldLeaf
          exact (hOld₀ u huOld).trans (hOldN u huOld).symm
      have hSameSupport :=
        hQ₀.1.eq_on_support_of_selected_leaves hQN₀.1 hEqualLeaves
      refine ⟨gN, QN, ?_⟩
      intro u hu
      exact (hSameSupport u hu).symm
    exact ⟨g₀, hPersistent, hOld₀, hProfile₀, hColour₀⟩

/-- For a fixed recurring complete profile/colour pair,
either one genuine next-leaf image persists through every finite
horizon, OR there are nonempty horizons where every realization
of this PARTICULAR pair has arbitrarily large image.

In the escape case the colour and the entire split record remain
fixed; an escaping witness in another colour is irrelevant. -/
theorem fixedJointProfileColour_persistent_or_escape
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat))
    (c : Fin (oldStageTailCut H m f) →
      Fin (oldStageTailCut H m f) → Bool)
    (hAll : ∀ n : Nat,
      HasJointProfileColourHorizon H K F f m p c n) :
    HasPersistentNextLeafWithJointProfileColour H K F f m p c ∨
    (∀ B : Nat, ∃ n : Nat,
      HasJointProfileColourHorizon H K F f m p c n ∧
      (∀ g : Nat → Nat,
        ReservedDiaryStage H K F (m + 1 + n) g →
        CofinalDiaryStageCompatible H m f g →
        (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
          g u.val = p u) →
        DiaryLowerBoundColors.singletonColour K
          (oldStageTailCut H m f) (g m) = c →
        B < g m)) := by
  classical
  by_cases hGood :
      HasPersistentNextLeafWithJointProfileColour H K F f m p c
  · exact Or.inl hGood
  · right
    intro B
    have hEscape : ∃ n : Nat,
        ∀ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g →
          CofinalDiaryStageCompatible H m f g →
          (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
            g u.val = p u) →
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (g m) = c →
          B < g m := by
      by_contra hNone
      push_neg at hNone
      have hBound :
          HasUniformNextLeafBoundWithJointProfileColour
            H K F f m p c := by
        refine ⟨B, ?_⟩
        intro n
        obtain ⟨g, Q, hOld, hProfile, hColour, hSmall⟩ := hNone n
        exact ⟨g, Q, hOld, hProfile, hColour, by omega⟩
      exact hGood
        ((persistent_jointProfileColour_iff_uniform_nextLeaf_bound
          hm p c).mpr hBound)
    obtain ⟨n, hEscapeN⟩ := hEscape
    exact ⟨n, hAll n, hEscapeN⟩

/-- Every finitely persistent old stage at a genuine source leaf
has ONE fixed full new split-generator profile p AND ONE fixed
complete mixed singleton-type colour c, realized at all horizons,
and INSIDE THIS SAME pair either a persistent next leaf exists
or numerical escape is forced at nonempty finite horizons.

This is the exact formal reduction left for a genuinely relative
geometric tail-richness proof. It does NOT exclude escape. -/
theorem persistent_stage_fixed_jointProfileColour_dichotomy
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (P : PersistentReservedDiaryStage H K F m f) :
    ∃ p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat),
      ∃ c : Fin (oldStageTailCut H m f) →
          Fin (oldStageTailCut H m f) → Bool,
        (∀ n : Nat,
          HasJointProfileColourHorizon H K F f m p c n) ∧
        (HasPersistentNextLeafWithJointProfileColour
          H K F f m p c ∨
          (∀ B : Nat, ∃ n : Nat,
            HasJointProfileColourHorizon H K F f m p c n ∧
            (∀ g : Nat → Nat,
              ReservedDiaryStage H K F (m + 1 + n) g →
              CofinalDiaryStageCompatible H m f g →
              (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
                g u.val = p u) →
              DiaryLowerBoundColors.singletonColour K
                (oldStageTailCut H m f) (g m) = c →
              B < g m))) := by
  obtain ⟨p, c, hAll⟩ :=
    persistent_stage_has_stable_profile_and_old_stage_colour hm P
  refine ⟨p, c, ?_, ?_⟩
  · exact hAll
  · exact fixedJointProfileColour_persistent_or_escape hm p c hAll

end DiaryLeafPriority
end ThreeUniformDiaries
