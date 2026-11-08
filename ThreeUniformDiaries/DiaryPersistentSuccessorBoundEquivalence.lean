import ThreeUniformDiaries.DiaryCofinalBoundedCountableFusion
import ThreeUniformDiaries.DiaryFixedProfileUniformBoundCriterion

/-!
# Track C: persistent next-leaf successor iff cofinally bounded choices

For a genuine new source leaf m, the conditional finite-to-countable
fusion gate has an EXACT elementary formulation. Existence of a
finitely persistent next reserved stage compatible with one old
support map f is equivalent to a *single* uniform numerical bound
on next-leaf images realized at cofinally high finite horizons.

In the forward implication choose the complete nonleaf-generator
profile prescribed by a persistent successor and apply the already
verified fixed-profile persistence/quantitative-bound equivalence.
Forget that profile and take the exact horizons n=N.
In the reverse implication restrict cofinally bounded witnesses to
all earlier finite horizons to obtain one finite next-image cover;
the verified finite-choice successor theorem then applies.

This characterizes the missing geometric assumption; it does NOT
assert that such a bound exists in any arbitrary target diary or
establish unconditional countable diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- An old-support-compatible persistent NEXT LEAF exists exactly
when new-leaf images can be chosen with ONE uniform bound along
cofinally many finite horizons. Requires only that m is a true
source leaf, not a supplied persistent old stage or generic range. -/
theorem persistentSuccessor_iff_cofinalBoundedNextLeafImages
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m) :
    (∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g) ↔
      HasCofinalBoundedNextLeafImages H K F f m := by
  classical
  constructor
  · rintro ⟨g0, P0, hOld0⟩
    let p :
        ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat) :=
      fun u => g0 u.val
    have hFixed : HasPersistentNextLeafWithFixedProfile H K F f m p :=
      ⟨g0, P0, hOld0, by intro u; rfl⟩
    have hUniform : HasUniformNextLeafBoundWithFixedProfile H K F f m p :=
      (persistent_fixedProfile_iff_uniform_nextLeaf_bound hm p).mp hFixed
    obtain ⟨B, hEvery⟩ := hUniform
    refine ⟨B, ?_⟩
    intro N
    obtain ⟨gN, QN, hOldN, _hProfile, hBound⟩ := hEvery N
    exact ⟨N, le_rfl, gN, QN, hOldN, hBound⟩
  · intro hCofinal
    exact exists_persistent_reserved_successor_of_finite_cover hm
      (finiteHorizonNextLeafCover_of_cofinal_bounded_images
        H K F f m hCofinal)

/-- In particular the original FINITE next-image cover has
exactly the same existence content as one finitely persistent
compatible next-leaf successor. No extra countable compactness
or target self-copy hypothesis is hidden in the statement. -/
theorem persistentSuccessor_iff_finiteHorizonNextLeafCover
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m) :
    (∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g) ↔
      FiniteHorizonNextLeafCover H K F m f := by
  constructor
  · intro hSucc
    apply finiteHorizonNextLeafCover_of_cofinal_bounded_images H K F f m
    exact (persistentSuccessor_iff_cofinalBoundedNextLeafImages hm).mp hSucc
  · intro hCover
    exact exists_persistent_reserved_successor_of_finite_cover hm hCover

end DiaryLeafPriority
end ThreeUniformDiaries
