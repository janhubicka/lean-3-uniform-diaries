import ThreeUniformDiaries.DiaryFirstLeafUniformAllHorizonColour
import ThreeUniformDiaries.DiaryFirstLeafWholeGenericReservedCones
import ThreeUniformDiaries.DiaryFiniteGoodOldCutCandidateColours
import ThreeUniformDiaries.DiaryFiniteCandidateOldColourDichotomy
import ThreeUniformDiaries.DiaryGenericTargetOldE5PatternCopy

/-!
# Track C: FIRST leaf — one ALL-HORIZON old support and whole GENERIC successor cones

English-first proof and adversarial audit:
  janhubicka/3-uniform-diaries PR #366.

The merged first-leaf all-horizon theorem chooses ONE
finitely persistent old marker support f and ONE complete
mixed oldStageTailCut singleton colour c with cofinally
high ACTUAL compatible reserved q=m+1+n stages for
EVERY future finite source horizon n and target bound.

The independently CI-verified marker-colour rigidity theorem
shows that for this SAME f its full old support cut is ≤3
and EVERY true target leaf has exactly the SAME complete
old-cut colour. Hence all true leaves have colour c.

The checked saturated old-cut tail lemma therefore makes
EVERY sufficiently high true F-range leaf an actual compatible
reserved IMMEDIATE m+1 successor over this very same f,
not merely leaves in an existentially picked generic colour
class. Arbitrarily high ENTIRE unordered induced generic
target leaf subcopies inside the ORIGINAL F range consist
completely of genuine immediate successors.

The single f,c are shared by ALL finite-horizon recurrence
witnesses and the WHOLE immediate successor generic copies.
No fixed next leaf image through all horizons, all-horizon
generic E5 witness cone, or countable unavoidability/BRD
conclusion is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- At the FIRST genuine source leaf, there is ONE finitely
persistent old marker support f and ONE complete old-cut colour c
such that all true target leaves have colour c, all high true
F-range leaves are full bare finite candidates, ALL finite
source horizons admit cofinally high genuine reserved witnesses
fixing f and colour c, EVERY sufficiently high F-range leaf
is an actual reserved IMMEDIATE successor, and every target
bound has a WHOLE induced unordered generic subcopy of these
genuine compatible immediate successors.

Crucially this reuses the SAME f,c for all the clauses; it is
not an invalid conjunction of independent existential f,c
choices. Nor does it imply one fixed new image through all
future source horizons. -/
theorem RoleDiary.exists_first_leaf_all_horizon_good_colour_and_whole_generic_successor_cones
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (hm : IsLeaf H m)
    (hFirst : countableDiaryLeafPrefix H m = ∅) :
    ∃ f : Nat → Nat,
      PersistentReservedDiaryStage H K
        (fun t : Nat => F t) m f ∧
      ∃ c : Fin (oldStageTailCut H m f) →
          Fin (oldStageTailCut H m f) → Bool,
        c ∈ goodOldCutCandidateColours H K
          (fun t : Nat => F t) f m ∧
        (∀ w : Nat, IsLeaf K w →
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) w = c) ∧
        (∀ w : Nat,
          oldStageTailCut H m f ≤ w →
          IsLeaf K w →
          (∃ t : Nat, w = F t) →
          FiniteNewLeafCandidateCondition H K
            (fun t : Nat => F t) m f w) ∧
        (∀ n M : Nat,
          ∃ t : Nat, ∃ g : Nat → Nat,
            M < F t ∧
            ReservedDiaryStage H K
              (fun t : Nat => F t) (m + 1 + n) g ∧
            CofinalDiaryStageCompatible H m f g ∧
            g m = F t ∧
            DiaryLowerBoundColors.singletonColour K
              (oldStageTailCut H m f) (F t) = c) ∧
        (∃ T : Nat, ∀ t : Nat, T ≤ F t →
          HasCompatibleReservedNextLeaf H K
            (fun t : Nat => F t) f m (F t)) ∧
        (∀ M : Nat,
          ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
            ∀ i : Nat,
              M < J i ∧
              IsLeaf K (J i) ∧
              (∃ t : Nat, J i = F t) ∧
              HasCompatibleReservedNextLeaf H K
                (fun t : Nat => F t) f m (J i)) := by
  classical
  obtain ⟨f,Pf,c,hAll,hSat⟩ :=
    DH.exists_first_leaf_uniform_all_horizon_old_support_and_colour
      DK G F hFLeaf m hm hFirst
  have hCut : oldStageTailCut H m f ≤ 3 :=
    first_leaf_oldStageTailCut_le_three Pf.1 hFirst
  obtain ⟨t₀,g₀,hHigh₀,Q₀,hOld₀,hNew₀,hColour₀⟩ :=
    hAll 0 (oldStageTailCut H m f)
  have hColourAll (w : Nat) (hw : IsLeaf K w) :
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) w = c := by
    have hSame :=
      DK.genuine_leaves_same_singletonColour_below_marker_cut
        (oldStageTailCut H m f) hCut (hFLeaf t₀) hw
    exact hSame.symm.trans hColour₀
  have QImmediate :
      ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g₀ :=
    Q₀.restrict (by omega)
  have hAnchor :
      HasCompatibleReservedNextLeaf H K
        (fun t : Nat => F t) f m (F t₀) :=
    ⟨g₀,QImmediate,hOld₀,hNew₀⟩
  have hFinite₀ :
      FiniteNewLeafCandidateCondition H K
        (fun t : Nat => F t) m f (F t₀) :=
    ((Pf.1.finite_candidate_iff_compatible_next_leaf DH hm).mpr
      hAnchor).1
  have hPalette :
      c ∈ goodOldCutCandidateColours H K
        (fun t : Nat => F t) f m := by
    simp only [goodOldCutCandidateColours, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨F t₀,Nat.le_of_lt hHigh₀,hFLeaf t₀,
      ⟨t₀,rfl⟩,hFinite₀,hColour₀⟩
  obtain ⟨T,hSatT⟩ := hSat
  have hEvery (t : Nat) (ht : T ≤ F t) :
      HasCompatibleReservedNextLeaf H K
        (fun t : Nat => F t) f m (F t) :=
    hSatT t ht (hColourAll (F t) (hFLeaf t))
  refine ⟨f,Pf,c,hPalette,hColourAll,?_,hAll,⟨T,hEvery⟩,?_⟩
  · intro w hw hwLeaf hwRange
    have hMember :
        DiaryLowerBoundColors.singletonColour K
          (oldStageTailCut H m f) w ∈
          goodOldCutCandidateColours H K
            (fun t : Nat => F t) f m := by
      rw [hColourAll w hwLeaf]
      exact hPalette
    exact (Pf.1.1.full_candidate_iff_good_oldCut_colour
      hm hw hwLeaf hwRange).mpr hMember
  · intro M
    obtain ⟨J,hRange,_hMask⟩ :=
      exists_generic_leaf_subcopy_in_prescribed_target_bounded_E5_pattern
        G K F hFLeaf 0 (max M T) (fun _ _ => false)
    refine ⟨J,?_⟩
    intro i
    obtain ⟨hHigh,_hAboveZero,hLeaf,t,hAtF⟩ := hRange i
    have hM : M < J i :=
      lt_of_le_of_lt (le_max_left M T) hHigh
    have hT : T ≤ J i :=
      (le_max_right M T).trans hHigh.le
    have hFT : T ≤ F t := by
      simpa only [← hAtF] using hT
    have hGood :
        HasCompatibleReservedNextLeaf H K
          (fun t : Nat => F t) f m (J i) := by
      simpa only [← hAtF] using hEvery t hFT
    exact ⟨hM,hLeaf,⟨t,hAtF⟩,hGood⟩

end DiaryLeafPriority
end ThreeUniformDiaries
