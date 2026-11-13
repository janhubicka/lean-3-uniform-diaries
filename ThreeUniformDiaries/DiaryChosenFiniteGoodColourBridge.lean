import ThreeUniformDiaries.DiaryFiniteGoodOldCutCandidateColours
import ThreeUniformDiaries.DiaryChosenOldSupportSaturatedGoodColour
import ThreeUniformDiaries.DiaryFiniteCandidateOldColourDichotomy

/-!
# Track C/D bridge: one chosen cofinal reserved colour is finite-candidate good

Fix a genuine new source leaf m with at least one old source leaf and an
arbitrary ORIGINAL unordered generic true-leaf embedding F. The verified
Track D theorem chooses one full reserved old support f and a complete
mixed old-cut colour c with cofinally many genuine compatible reserved
successors, eventually all true F-range leaves in c being reserved
successors. Track C's exact finite-colour criterion now gives more:

* c belongs to the FINITE palette of high complete finite-candidate
  colours for this chosen f;
* EVERY true F-range leaf of colour c above the OLD cut B is a complete
  finite candidate, with NO additional per-colour threshold;
* beyond a possibly larger threshold T, every such leaf is a genuinely
  compatible RESERVED immediate successor; and
* these reserved successors occur cofinally.

This is a precise distinction between ordinary finite admissibility
and the independent future-order reserve. It DOES NOT assert c contains
an induced generic subcopy or that a fixed image persists through
later source horizons. No all-source-horizon fusion, countable
unavoidability or big Ramsey degree conclusion is implied.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A CHOSEN complete reserved old stage and ONE cofinally recurrent
complete old-cut colour jointly satisfy the whole finite-candidate
colour criterion from Track C and the stronger eventual reserved
successor condition from Track D. All target leaves belong to the
ORIGINAL prescribed F range. The old support f and colour c are
chosen together; neither can be prescribed in advance. -/
theorem RoleDiary.exists_chosen_old_support_with_uniform_high_finite_candidates
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (hm : IsLeaf H m)
    (hOldNonempty : (countableDiaryLeafPrefix H m).Nonempty) :
    ∃ f : Nat → Nat,
      ReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      ∃ c : Fin (oldStageTailCut H m f) →
          Fin (oldStageTailCut H m f) → Bool,
        c ∈ goodOldCutCandidateColours H K (fun t : Nat => F t) f m ∧
        (∀ w : Nat,
          oldStageTailCut H m f ≤ w →
          IsLeaf K w →
          (∃ t : Nat, w = F t) →
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) w = c →
          FiniteNewLeafCandidateCondition H K
            (fun t : Nat => F t) m f w) ∧
        (∀ M : Nat, ∃ t : Nat,
          M < F t ∧
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (F t) = c ∧
          HasCompatibleReservedNextLeaf H K
            (fun t : Nat => F t) f m (F t)) ∧
        (∃ T : Nat, ∀ t : Nat, T ≤ F t →
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (F t) = c →
          HasCompatibleReservedNextLeaf H K
            (fun t : Nat => F t) f m (F t)) := by
  classical
  obtain ⟨f, Pf, c, hCofinal, hSaturated⟩ :=
    DH.exists_chosen_old_support_with_saturated_good_colour
      DK G F hFLeaf m hm hOldNonempty
  have hInPalette :
      c ∈ goodOldCutCandidateColours H K
        (fun t : Nat => F t) f m := by
    obtain ⟨t, hHigh, hColour, hCompat⟩ :=
      hCofinal (oldStageTailCut H m f)
    have hFinite :
        FiniteNewLeafCandidateCondition H K
          (fun t : Nat => F t) m f (F t) :=
      ((Pf.finite_candidate_iff_compatible_next_leaf DH hm).mpr
        hCompat).1
    simp only [goodOldCutCandidateColours, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨F t, Nat.le_of_lt hHigh, hFLeaf t, ⟨t, rfl⟩,
      hFinite, hColour⟩
  refine ⟨f, Pf, c, hInPalette, ?_, hCofinal, hSaturated⟩
  intro w hw hwLeaf hwRange hwColour
  have hColourGood :
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) w ∈
      goodOldCutCandidateColours H K
        (fun t : Nat => F t) f m := by
    simpa only [hwColour] using hInPalette
  exact (Pf.1.full_candidate_iff_good_oldCut_colour
    hm hw hwLeaf hwRange).mpr hColourGood

end DiaryLeafPriority
end ThreeUniformDiaries
