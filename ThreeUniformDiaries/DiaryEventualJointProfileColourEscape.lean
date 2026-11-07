import ThreeUniformDiaries.DiaryFixedJointProfileColourEscape

/-!
# Track D: escape is EVENTUAL in one fixed complete mixed-type fibre

The fixed joint split-generator profile p and complete mixed singleton
colour c from the checked old-stage stabilisation lemma can be
realized at every finite continuation horizon, but their leaf images
may have to escape. The predecessor dichotomy gave, for each B,
one nonempty horizon at which every (p,c)-candidate lies above B.

This stronger consequence shows the escape persists at ALL later
horizons. Every later reserved realization restricts to a valid
realization at the earlier horizon without changing the chosen
new-leaf image or the full old support/profile/colour.

Moreover, even when the prescribed original leaf map F is UNORDERED,
its image of any fixed finite index interval is bounded in Nat.
Hence eventual numerical escape entails eventual escape beyond every
fixed PREIMAGE-INDEX cutoff as well. No monotonicity or injectivity
of F is used for this direction.

This sharpens the negative branch of the conditional dichotomy,
without proving that it cannot occur in actual role diaries.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Within ONE complete split-generator profile and ONE actual
mixed singleton-type mask, absence of a persistent successor forces
uniform image escape at ALL sufficiently high finite horizons.

The hAll hypothesis ensures NONVACUITY: the fixed fibre has genuine
reserved realizations at every finite horizon. -/
theorem fixedJointProfileColour_persistent_or_eventually_escape
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat))
    (c : Fin (oldStageTailCut H m f) →
      Fin (oldStageTailCut H m f) → Bool)
    (hAll : ∀ n : Nat,
      HasJointProfileColourHorizon H K F f m p c n) :
    HasPersistentNextLeafWithJointProfileColour H K F f m p c ∨
    (∀ B : Nat, ∃ N : Nat,
      ∀ n : Nat, N ≤ n →
        ∀ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g →
          CofinalDiaryStageCompatible H m f g →
          (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
            g u.val = p u) →
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (g m) = c →
          B < g m) := by
  rcases fixedJointProfileColour_persistent_or_escape
      hm p c hAll with hGood | hEsc
  · exact Or.inl hGood
  · right
    intro B
    obtain ⟨N, _hReal, hEscN⟩ := hEsc B
    refine ⟨N, ?_⟩
    intro n hNn g Q hOld hProfile hColour
    have QN : ReservedDiaryStage H K F (m + 1 + N) g :=
      Q.restrict (by omega)
    exact hEscN g QN hOld hProfile hColour

/-- In the escaping branch, at all sufficiently late horizons EVERY
index t realizing the new-leaf image g(m)=F(t) is >= any previously
chosen finite index cutoff T. This works for an arbitrary unordered
F, without a new genericity or injectivity hypothesis.

The statement concerns all actual future (p,c)-realizations; they
exist at every horizon by hAll. -/
theorem fixedJointProfileColour_persistent_or_eventual_index_escape
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat))
    (c : Fin (oldStageTailCut H m f) →
      Fin (oldStageTailCut H m f) → Bool)
    (hAll : ∀ n : Nat,
      HasJointProfileColourHorizon H K F f m p c n) :
    HasPersistentNextLeafWithJointProfileColour H K F f m p c ∨
    (∀ T : Nat, ∃ N : Nat,
      ∀ n : Nat, N ≤ n →
        ∀ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g →
          CofinalDiaryStageCompatible H m f g →
          (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
            g u.val = p u) →
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (g m) = c →
          ∀ t : Nat, g m = F t → T ≤ t) := by
  classical
  rcases fixedJointProfileColour_persistent_or_eventually_escape
      hm p c hAll with hGood | hEscape
  · exact Or.inl hGood
  · right
    intro T
    obtain ⟨N, hEscN⟩ := hEscape ((Finset.range T).sup F)
    refine ⟨N, ?_⟩
    intro n hNn g Q hOld hProfile hColour t hEq
    have hLarge : ((Finset.range T).sup F) < g m :=
      hEscN n hNn g Q hOld hProfile hColour
    by_contra hNot
    have ht : t < T := by omega
    have hSmall : F t ≤ (Finset.range T).sup F :=
      Finset.le_sup (f := F) (Finset.mem_range.mpr ht)
    rw [hEq] at hLarge
    omega

end DiaryLeafPriority
end ThreeUniformDiaries
