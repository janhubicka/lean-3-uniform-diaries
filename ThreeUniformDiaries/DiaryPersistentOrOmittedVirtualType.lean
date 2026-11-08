import ThreeUniformDiaries.DiaryEscapingVirtualTypeOmission
import ThreeUniformDiaries.DiaryCoherentVirtualMixedType
import ThreeUniformDiaries.DiaryEventualJointProfileColourEscape

/-!
# Track D: persistent next leaf OR an omitted coherent full mixed-type limit

This ties together the old-stage complete nonleaf-profile/full mixed
finite-colour stabilization, the verified sharp persistence-escape
dichotomy and the genuine full-diary S1 obstruction to realizing the
infinite virtual type of an escaping sequence of target leaves.

For a fixed finitely persistent old reserved stage and genuine new
source leaf m, choose ONE complete new nonleaf generator record p
and ONE complete mixed singleton colour c0 below the old-stage cut.
Actual compatible reserved witnesses with this SAME (p,c0) exist
through every finite future horizon.

Either one next-leaf image persists, OR we can choose an actual
genuine target leaf at each finite horizon such that their images
eventually escape every finite target bound. Finite-colour
compactness over ALL target cuts yields a coherent virtual full
mixed singleton type c∞ recurring at arbitrarily late horizons,
still with the same old support, the same split record p and
the same original finite colour c0. In a full RoleDiary target
the S1 axiom then shows NO target leaf realizes c∞.

The omitted type is a NECESSARY symptom of the escape branch,
not a contradiction. It does not exclude escape or prove the
unconditional countable diary unavoidability theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A finitely persistent old diary stage at a genuine next source
leaf admits one fixed complete new nonleaf generator profile p and
one finite complete mixed colour c0, realized at every horizon.

Within that SAME fibre, either there is a persistent genuine
new-leaf successor, or there is a coherent ALL-CUT virtual
mixed singleton type c∞ satisfying:
* its restriction at the old-stage cut equals the original c0;
* every finite prefix c∞(B) is realized at arbitrarily late
  source horizons, fixing the old support and full nonleaf record
  AND retaining the original finite c0;
* no actual genuine target leaf realizes all c∞(B).

This exposes the exact saturation obstacle still left after
joint finite-type stabilization; it supplies no relative
bounded new-leaf realization or countable embedding. -/
theorem persistent_stage_persistent_or_omitted_virtual_mixed_type
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (DK : RoleDiary K)
    (hm : IsLeaf H m)
    (P : PersistentReservedDiaryStage H K F m f) :
    ∃ p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat),
      ∃ c0 : Fin (oldStageTailCut H m f) →
        Fin (oldStageTailCut H m f) → Bool,
        (∀ n : Nat,
          HasJointProfileColourHorizon H K F f m p c0 n) ∧
        (HasPersistentNextLeafWithJointProfileColour
          H K F f m p c0 ∨
        ∃ c∞ : (B : Nat) → Fin B → Fin B → Bool,
          (∀ (B : Nat) (x y : Fin B),
            c∞ (B + 1) x.castSucc y.castSucc = c∞ B x y) ∧
          c∞ (oldStageTailCut H m f) = c0 ∧
          (∀ B N : Nat, ∃ n : Nat, N ≤ n ∧
            ∃ g : Nat → Nat,
              ReservedDiaryStage H K F (m + 1 + n) g ∧
              CofinalDiaryStageCompatible H m f g ∧
              (∀ u : {u : Nat //
                u ∈ newNonleafGeneratorSupport H m},
                g u.val = p u) ∧
              DiaryLowerBoundColors.singletonColour K
                (oldStageTailCut H m f) (g m) = c0 ∧
              DiaryLowerBoundColors.singletonColour K B (g m) =
                c∞ B) ∧
          (¬ ∃ v : Nat, IsLeaf K v ∧
            ∀ B : Nat,
              DiaryLowerBoundColors.singletonColour K B v = c∞ B)) := by
  classical
  obtain ⟨p, c0, hAll⟩ :=
    persistent_stage_has_stable_profile_and_old_stage_colour hm P
  refine ⟨p, c0, hAll, ?_⟩
  rcases fixedJointProfileColour_persistent_or_eventually_escape
      hm p c0 hAll with hPersistent | hEscape
  · exact Or.inl hPersistent
  · right
    let g : Nat → Nat → Nat :=
      fun n => Classical.choose (hAll n)
    have hg (n : Nat) :
        ReservedDiaryStage H K F (m + 1 + n) (g n) ∧
        CofinalDiaryStageCompatible H m f (g n) ∧
        (∀ u : {u : Nat //
          u ∈ newNonleafGeneratorSupport H m},
          g n u.val = p u) ∧
        DiaryLowerBoundColors.singletonColour K
          (oldStageTailCut H m f) (g n m) = c0 :=
      Classical.choose_spec (hAll n)
    let v : Nat → Nat := fun n => g n m
    have hv : ∀ n : Nat, IsLeaf K (v n) := by
      intro n
      have hmSelected :
          m ∈ countableDiaryLeafPrefix H (m + 1 + n) :=
        (mem_countableDiaryLeafPrefix_iff H (m + 1 + n) m).mpr
          ⟨hm.1, by omega, hm⟩
      have hmSupported :
          m ∈ countableDiaryFiniteSupport H (m + 1 + n) :=
        mem_finiteLeafMeetSupport_leaf H
          (countableDiaryLeafPrefix H (m + 1 + n))
          m hmSelected
      exact (hg n).1.1.leaf_role m hmSupported hm
    have hEscaping : ∀ B : Nat, ∃ N : Nat,
        ∀ n : Nat, N ≤ n → B < v n := by
      intro B
      obtain ⟨N, hN⟩ := hEscape B
      refine ⟨N, ?_⟩
      intro n hn
      exact hN n hn (g n) (hg n).1
        (hg n).2.1 (hg n).2.2.1 (hg n).2.2.2
    obtain ⟨c∞, hProject, hRecur⟩ :=
      exists_coherent_cofinal_mixed_singleton_type K v
    have hAtOldCut :
        c∞ (oldStageTailCut H m f) = c0 := by
      obtain ⟨n, _hn, hMask⟩ :=
        hRecur (oldStageTailCut H m f) 0
      exact hMask.symm.trans (hg n).2.2.2
    have hOmitted :
        ¬ ∃ w : Nat, IsLeaf K w ∧
          ∀ B : Nat,
            DiaryLowerBoundColors.singletonColour K B w =
              c∞ B :=
      DK.escaping_recurrent_full_mixed_type_omitted
        v hv hEscaping c∞ hRecur
    refine ⟨c∞, hProject, hAtOldCut, ?_, hOmitted⟩
    intro B N
    obtain ⟨n, hn, hMask⟩ := hRecur B N
    exact ⟨n, hn, g n, (hg n).1, (hg n).2.1,
      (hg n).2.2.1, (hg n).2.2.2, hMask⟩

end DiaryLeafPriority
end ThreeUniformDiaries
