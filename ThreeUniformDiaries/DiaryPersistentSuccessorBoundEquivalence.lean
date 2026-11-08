import ThreeUniformDiaries.DiaryCofinalBoundedCountableFusion

/-!
# Track C: persistent next-leaf successor iff cofinally bounded choices

For a genuine new source leaf m, the conditional finite-to-countable
fusion gate has an EXACT elementary formulation. Existence of a
finitely persistent next reserved stage compatible with one old
support map f is equivalent to a *single* uniform numerical bound
on next-leaf images realized at cofinally high finite horizons.

For the forward implication, any persistent successor comes with
compatible maps at every horizon. Compatibility on the entire
new-stage support fixes the new leaf image and the old support.
Hence the persistent successor's own leaf image gives a bound.
For the reverse implication, cofinally bounded horizon witnesses
supply a finite next-image cover, and finite-choice persistence
constructs the desired successor.

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
    refine ⟨g0 m, ?_⟩
    intro N
    obtain ⟨gN, QN, hCompat⟩ := P0.2 N
    have hOldN : CofinalDiaryStageCompatible H m f gN :=
      CofinalDiaryStageCompatible.trans (Nat.le_succ m) hOld0 hCompat
    have hmSupported :
        m ∈ countableDiaryFiniteSupport H (m + 1) :=
      mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H (m + 1)) m
        ((mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
          ⟨hm.1, by omega, hm⟩)
    have hBound : gN m ≤ g0 m := by
      rw [hCompat m hmSupported]
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
