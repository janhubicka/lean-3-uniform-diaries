import ThreeUniformDiaries.DiaryPersistentSuccessorBoundEquivalence

/-!
# Track C: no eventual escape IFF a persistent compatible successor

English proof and adversarial quantifier audit:
  janhubicka/3-uniform-diaries PR #259
  notes/track_c_nonescape_iff_persistence_english_20261108.md

A cofinal numerical bound for the next genuine leaf is precisely
the classical NEGATION of eventual escape past every numerical
threshold, for the same fixed old support map f. The abstract
quantifier equivalence needs neither IsLeaf nor nonempty horizon
fibres; under the genuine IsLeaf condition it composes with the
merged persistent-successor ↔ cofinal-bound theorem (#1231).

This is an exact *reformulation*, not a proof that escape is absent,
nor a proof of unconditional countable diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A fixed numerical bound appearing at arbitrarily high actual
old-compatible reserved horizons is exactly the negation of eventual
all-horizon numerical escape. No source-leaf or old-stage persistence
hypothesis is used, since this is purely quantified logic.

Even when late horizon fibres are empty, both sides are correct:
the cofinal bounded side is false and escape is vacuously true. -/
theorem cofinalBoundedNextLeafImages_iff_not_uniform_escape
    (H K : Ordered3Graph Nat) (F f : Nat → Nat) (m : Nat) :
    HasCofinalBoundedNextLeafImages H K F f m ↔
      ¬ (∀ B : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
        ∀ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g →
          CofinalDiaryStageCompatible H m f g →
          B < g m) := by
  classical
  constructor
  · rintro ⟨B, hBound⟩ hEscape
    obtain ⟨N, hEveryLarge⟩ := hEscape B
    obtain ⟨n, hn, g, Q, hOld, hSmall⟩ := hBound N
    have hLarge : B < g m := hEveryLarge n hn g Q hOld
    omega
  · intro hNotEscape
    by_contra hNoBound
    apply hNotEscape
    intro B
    by_contra hNoThreshold
    apply hNoBound
    refine ⟨B, ?_⟩
    intro N
    by_contra hNoWitness
    apply hNoThreshold
    refine ⟨N, ?_⟩
    intro n hn g Q hOld
    by_contra hNotFar
    apply hNoWitness
    exact ⟨n, hn, g, Q, hOld, by omega⟩

/-- At a genuine source leaf, a finitely persistent reserved
successor agreeing on all of the old S1/S2 support exists IFF
eventual all-horizon escape of the next leaf is FALSE.

This has no assumption that the old stage is already persistent:
negation of escape itself forces cofinally high genuine witnesses.
It does not establish the negation of escape in any target diary. -/
theorem persistentSuccessor_iff_not_uniform_escape
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m) :
    (∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g) ↔
      ¬ (∀ B : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
        ∀ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g →
          CofinalDiaryStageCompatible H m f g →
          B < g m) :=
  (persistentSuccessor_iff_cofinalBoundedNextLeafImages
    (H := H) (K := K) (F := F) (f := f) (m := m) hm).trans
    (cofinalBoundedNextLeafImages_iff_not_uniform_escape H K F f m)

end DiaryLeafPriority
end ThreeUniformDiaries
