import ThreeUniformDiaries.DiaryFirstLeafUniformAllHorizonColour
import ThreeUniformDiaries.DiaryPersistentUniformEscape

/-!
# Track C: FIRST source leaf — all-horizon good colour, persistent next leaf OR uniform escape

English-first adversarial proof and audit:
  janhubicka/3-uniform-diaries PR #364.

For a genuine FIRST source leaf m (no earlier selected source
leaves), the independently checked all-horizon base theorem
selects ONE finitely persistent marker-only old reserved stage
f and ONE complete mixed oldStageTailCut singleton colour c,
with ACTUAL reserved horizon witnesses of this SAME colour
cofinally far out at EVERY future finite source horizon.

The independently checked persistent-next-leaf-or-uniform-escape
theorem applies to this SAME f. Either a genuine persistent
reserved m+1 successor fixes the old support, or EVERY
compatible reserved horizon stage must send m beyond each
fixed numerical bound at all sufficiently late horizons.

In the escape branch, the first-leaf all-horizon theorem
supplies an ACTUAL genuine reserved stage in the chosen
COMPLETE colour c at EVERY sufficiently late horizon, above
the bound. Thus the escape certificate is NONVACUOUS even
within the SAME fixed colour c.

Neither branch is asserted to hold unconditionally in place of
the other. No generic E5 subcopy/bipolar pair in c, no final
countable unavoidability and no exact BRD theorem is claimed.
The original prescribed F range remains UNORDERED generic.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- At the first genuine source leaf m one COMPLETE old
finitely persistent marker support f and one mixed singleton
colour c work at ALL future finite horizons.

Either f has an ACTUAL compatible finitely persistent successor
at m+1, or for every B all sufficiently long genuine reserved
extensions of f send m to a target level >B. In the latter case,
there is STILL a real c-coloured compatible reserved stage at
each such horizon, with new image in the ORIGINAL F range above
B. In both branches the chosen c is eventually saturated for
IMMEDIATE reserved successor images.

This is a finite-stage relative persistence-or-escape theorem,
not a countable diary embedding or a generic-colour richness result. -/
theorem RoleDiary.exists_first_leaf_good_colour_persistent_or_uniform_escape
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
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (F t) = c →
          HasCompatibleReservedNextLeaf H K
            (fun t : Nat => F t) f m (F t)) ∧
        ((∃ g : Nat → Nat,
            PersistentReservedDiaryStage H K
              (fun t : Nat => F t) (m + 1) g ∧
            CofinalDiaryStageCompatible H m f g) ∨
         (∀ B : Nat, ∃ N : Nat,
            ∀ n : Nat, N ≤ n →
              (∃ t : Nat, ∃ g : Nat → Nat,
                B < F t ∧
                ReservedDiaryStage H K
                  (fun t : Nat => F t) (m + 1 + n) g ∧
                CofinalDiaryStageCompatible H m f g ∧
                g m = F t ∧
                DiaryLowerBoundColors.singletonColour K
                  (oldStageTailCut H m f) (F t) = c) ∧
              (∀ g : Nat → Nat,
                ReservedDiaryStage H K
                  (fun t : Nat => F t) (m + 1 + n) g →
                CofinalDiaryStageCompatible H m f g →
                B < g m))) := by
  obtain ⟨f,Pf,c,hAll,hSat⟩ :=
    DH.exists_first_leaf_uniform_all_horizon_old_support_and_colour
      DK G F hFLeaf m hm hFirst
  refine ⟨f,Pf,c,hAll,hSat,?_⟩
  rcases persistent_next_leaf_or_eventual_uniform_escape
    hm Pf with hPersistent | hEscape
  · exact Or.inl hPersistent
  · right
    intro B
    obtain ⟨N,hAfter⟩ := hEscape B
    refine ⟨N,?_⟩
    intro n hn
    constructor
    · exact hAll n B
    · intro g Q hCompat
      exact (hAfter n hn).2 g Q hCompat

end DiaryLeafPriority
end ThreeUniformDiaries
