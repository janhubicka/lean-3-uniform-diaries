import ThreeUniformDiaries.DiaryCoherentVirtualMixedType
import ThreeUniformDiaries.DiaryEscapingVirtualTypeOmission

/-!
# Track C: every infinite true-leaf range has a coherent omitted cofinal type

English proof and adversarial audit: janhubicka/3-uniform-diaries PR #280.

In every full RoleDiary target and every injected countably infinite range
of genuine leaves, there is a projection-coherent complete mixed singleton
type cofinally realized at each finite cut in that very range, yet omitted
by every genuine target leaf. This follows from the existing checked
finite-palette diagonalization and the checked full-diary S1 separation.

This rules out a blanket countable type-realization principle; it does NOT
disprove relative diary unavoidability or produce a bad reserved old stage.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Any infinite injected range of true leaves in a full RoleDiary gives
a coherent virtual complete mixed singleton type whose every finite cut
recurs cofinally in that original range, but with NO realizing true leaf.

Injectivity suffices; the range need not be numerically increasing or
induced-generic. Full RoleDiary and true target leaves are essential. -/
theorem RoleDiary.exists_coherent_cofinal_omitted_mixed_singleton_type
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (F : Nat → Nat) (hInj : Function.Injective F)
    (hLeaf : ∀ n : Nat, IsLeaf K (F n)) :
    ∃ c : (B : Nat) → Fin B → Fin B → Bool,
      (∀ (B : Nat) (x y : Fin B),
        c (B + 1) x.castSucc y.castSucc = c B x y) ∧
      (∀ (B N : Nat), ∃ n : Nat, N ≤ n ∧
        DiaryLowerBoundColors.singletonColour K B (F n) = c B) ∧
      (¬ ∃ u : Nat, IsLeaf K u ∧
        ∀ B : Nat,
          DiaryLowerBoundColors.singletonColour K B u = c B) := by
  obtain ⟨c, hCoherent, hRecur⟩ :=
    exists_coherent_cofinal_mixed_singleton_type K F
  refine ⟨c, hCoherent, hRecur, ?_⟩
  exact DK.injective_leaf_recurrent_full_mixed_type_omitted
    F hLeaf hInj c hRecur

/-- A universal countable-saturation shortcut is IMPOSSIBLE in any
injected infinite true-leaf range of a full RoleDiary: one coherent
cofinally finitely realized type has no actual target true-leaf witness.

This statement is about arbitrary complete singleton types, NOT a
particular prescribed old-stage E2/E3 incidence fibre. -/
theorem RoleDiary.not_all_cofinal_coherent_mixed_types_realized
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (F : Nat → Nat) (hInj : Function.Injective F)
    (hLeaf : ∀ n : Nat, IsLeaf K (F n)) :
    ¬ (∀ c : (B : Nat) → Fin B → Fin B → Bool,
        (∀ (B : Nat) (x y : Fin B),
          c (B + 1) x.castSucc y.castSucc = c B x y) →
        (∀ (B N : Nat), ∃ n : Nat, N ≤ n ∧
          DiaryLowerBoundColors.singletonColour K B (F n) = c B) →
        ∃ u : Nat, IsLeaf K u ∧
          ∀ B : Nat,
            DiaryLowerBoundColors.singletonColour K B u = c B) := by
  intro hRealize
  obtain ⟨c, hCoherent, hRecur, hOmitted⟩ :=
    DK.exists_coherent_cofinal_omitted_mixed_singleton_type
      F hInj hLeaf
  exact hOmitted (hRealize c hCoherent hRecur)

end DiaryLeafPriority
end ThreeUniformDiaries
