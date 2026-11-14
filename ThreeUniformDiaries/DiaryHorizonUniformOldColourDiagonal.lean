import ThreeUniformDiaries.DiaryTwoParameterFiniteOldSupportChoice
import ThreeUniformDiaries.DiaryReservedOldColourTailDichotomy

/-!
# Track A: jointly stabilise old support AND its full old-cut colour over ALL horizons

English-first adversarial proof: 3-uniform-diaries PR #355.

Under the UNPROVED existence of one finite old-supported image
profile palette covering actual reserved witnesses at every
future source horizon and target numerical bound, the verified
two-parameter support-profile diagonal selects ONE literal
old f which is finitely persistent and has cofinally high
reserved q-stage images at EVERY horizon.

A SECOND, independent finite-palette diagonal selects ONE
complete mixed singleton colour c at the exact OLD-SUPPORT cut
oldStageTailCut H m f, not the shorter leaf-only cut.
All horizons q=m+1+n and target numerical bounds M have
genuine compatible reserved witnesses g with g(m)=F(t)>M
and this SAME complete old-cut colour c.

At n=M=0 there is one actual reserved next-leaf anchor;
the checked tail replacement theorem then eventually makes
all F-range true c leaves genuine compatible IMMEDIATE
successors over f. No selected c is proved generic-rich,
and no fixed new leaf survives all later horizons.

The finite old-profile W is still hypothetical; the merged
all-horizon old-support-escape theorem shows W cannot be
selected uniformly before arbitrary unordered generic
refinements. No countable diary unavoidability is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Given ONE fixed old support f with arbitrarily late actual
reserved continuations at EVERY finite horizon, there is a SINGLE
complete oldStageTailCut mixed singleton colour appearing
cofinally among genuine compatible continuations at EVERY horizon.

The output has quantifiers ∃c ∀n,M ∃t,g. Different horizons
and target bounds may still require different new images g(m).
The existing finite two-parameter choice theorem applies since
genuine reserved stages RESTRICT to lower horizons. -/
theorem exists_one_oldCut_colour_cofinal_across_all_finite_horizons
    {H K : Ordered3Graph Nat}
    (F f : Nat → Nat) (m : Nat)
    (hAll : ∀ n M : Nat,
      ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        ReservedDiaryStage H K F (m + 1 + n) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        g m = F t) :
    ∃ c : Fin (oldStageTailCut H m f) →
        Fin (oldStageTailCut H m f) → Bool,
      ∀ n M : Nat,
        ∃ t : Nat, ∃ g : Nat → Nat,
          M < F t ∧
          ReservedDiaryStage H K F (m + 1 + n) g ∧
          CofinalDiaryStageCompatible H m f g ∧
          g m = F t ∧
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (F t) = c := by
  classical
  let B := oldStageTailCut H m f
  let Colour := Fin B → Fin B → Bool
  let P : Colour → Nat → Nat → Prop := fun c n M =>
    ∃ t : Nat, ∃ g : Nat → Nat,
      M < F t ∧
      ReservedDiaryStage H K F (m + 1 + n) g ∧
      CofinalDiaryStageCompatible H m f g ∧
      g m = F t ∧
      DiaryLowerBoundColors.singletonColour K B (F t) = c
  have hDownN : ∀ (c : Colour) (n k M : Nat),
      k ≤ n → P c n M → P c k M := by
    intro c n k M hkn
    rintro ⟨t, g, hHigh, Q, hKeep, hAt, hColour⟩
    exact ⟨t, g, hHigh, Q.restrict (by omega),
      hKeep, hAt, hColour⟩
  have hDownM : ∀ (c : Colour) (n M L : Nat),
      L ≤ M → P c n M → P c n L := by
    intro c n M L hLM
    rintro ⟨t, g, hHigh, Q, hKeep, hAt, hColour⟩
    exact ⟨t, g, lt_of_le_of_lt hLM hHigh,
      Q, hKeep, hAt, hColour⟩
  have hCover : ∀ n M : Nat,
      ∃ c : Colour, c ∈ (Finset.univ : Finset Colour) ∧
        P c n M := by
    intro n M
    obtain ⟨t, g, hHigh, Q, hKeep, hAt⟩ := hAll n M
    refine ⟨DiaryLowerBoundColors.singletonColour K B (F t),
      Finset.mem_univ _, t, g, hHigh, Q, hKeep, hAt, rfl⟩
  obtain ⟨c, _hc, hColour⟩ :=
    finite_choice_persistent_of_two_downward_parameters
      (Finset.univ : Finset Colour) P hDownN hDownM hCover
  exact ⟨c, hColour⟩

/-- A finite palette of ACTUAL old-supported profiles, uniformly
covering cofinally high reserved witnesses at each source horizon,
selects one finitely persistent actual old stage f AND one old-cut
full singleton colour c such that ALL future horizons and ALL
target numerical cutoffs have cofinally late genuine reserved
witnesses of that SAME c compatible with f.

The colour also has a genuine immediate reserved anchor.
Consequently it is EVENTUALLY SATURATED with actual immediate
reserved successors among original F-range true leaves.

This remains CONDITIONAL on a common finite old-profile palette.
Neither cofinal persistence within c nor eventual saturation
proves c contains a generic subcopy, nor one fixed g(m) remains
compatible throughout future horizons. -/
theorem exists_persistent_old_support_and_saturated_colour_all_horizons_of_finite_profile_cover
    {H K : Ordered3Graph Nat}
    (F : Nat → Nat) (m : Nat)
    (hm : IsLeaf H m)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (W : Finset
      ({u : Nat // u ∈ countableDiaryFiniteSupport H m} → Nat))
    (hCover : ∀ n M : Nat,
      ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        ReservedDiaryStage H K F (m + 1 + n) g ∧
        g m = F t ∧
        (fun u : {u : Nat //
          u ∈ countableDiaryFiniteSupport H m} => g u.val) ∈ W) :
    ∃ f : Nat → Nat,
      PersistentReservedDiaryStage H K F m f ∧
      ∃ c : Fin (oldStageTailCut H m f) →
          Fin (oldStageTailCut H m f) → Bool,
        (∀ n M : Nat,
          ∃ t : Nat, ∃ g : Nat → Nat,
            M < F t ∧
            ReservedDiaryStage H K F (m + 1 + n) g ∧
            CofinalDiaryStageCompatible H m f g ∧
            g m = F t ∧
            DiaryLowerBoundColors.singletonColour K
              (oldStageTailCut H m f) (F t) = c) ∧
        (∃ T : Nat, ∀ t : Nat,
          T ≤ F t →
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (F t) = c →
          HasCompatibleReservedNextLeaf H K F f m (F t)) := by
  classical
  obtain ⟨f, hPersistent, hAll⟩ :=
    exists_one_old_support_for_all_finite_horizons_of_finite_profile_palette
      F m W hCover
  obtain ⟨c, hAllColour⟩ :=
    exists_one_oldCut_colour_cofinal_across_all_finite_horizons
      F f m hAll
  obtain ⟨t₀, g₀, _hHigh₀, Q₀, hOld₀, hAt₀, hColour₀⟩ :=
    hAllColour 0 0
  have hAnchor :
      HasCompatibleReservedNextLeaf H K F f m (F t₀) := by
    refine ⟨g₀, ?_, hOld₀, hAt₀⟩
    simpa only [Nat.add_zero] using Q₀
  refine ⟨f, hPersistent, c, hAllColour, F t₀, ?_⟩
  intro t hLater hColour
  exact compatible_reserved_nextLeaf_tail_of_oldCut_colour
    hm hAnchor hLater (hFLeaf t) ⟨t, rfl⟩
    (hColour₀.trans hColour.symm)

end DiaryLeafPriority
end ThreeUniformDiaries
