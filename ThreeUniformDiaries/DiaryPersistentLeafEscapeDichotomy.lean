import ThreeUniformDiaries.DiaryFiniteCandidatePersistentFusion

/-!
# Persistent next-leaf choice or unavoidable escape to infinity

For a finitely persistent old stage and a genuine new source leaf,
either some fixed new target leaf image yields a finitely persistent
successor, or the next target leaf image MUST escape beyond every
prescribed bound at a sufficiently long finite horizon.

The second alternative is NONVACUOUS: finite persistence ensures an
old-compatible reserved extension really exists at each finite
horizon. The absence of a persistent successor means that no finite
set of next-leaf images can hit all horizons, by the verified finite
cover successor theorem.

This is an exact qualitative diagnosis of the remaining obstruction.
It does not rule out escape for actual diaries or construct a safe
next image, and it does not prove countable unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- At a finitely persistent leaf step, failure to stabilize ONE new
target leaf image forces uniformly large next-leaf images at some
finite horizon beyond every proposed bound. The relevant horizon
always has a genuine reserved realization fixing the old support. -/
theorem persistent_next_leaf_or_eventual_escape
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (P : PersistentReservedDiaryStage H K F m f) :
    (∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g) ∨
    (∀ B : Nat, ∃ n : Nat,
      (∃ g : Nat → Nat,
        ReservedDiaryStage H K F (m + 1 + n) g ∧
        CofinalDiaryStageCompatible H m f g) ∧
      (∀ g : Nat → Nat,
        ReservedDiaryStage H K F (m + 1 + n) g →
        CofinalDiaryStageCompatible H m f g →
        B < g m)) := by
  classical
  by_cases hSuccess :
      ∃ g : Nat → Nat,
        PersistentReservedDiaryStage H K F (m + 1) g ∧
        CofinalDiaryStageCompatible H m f g
  · exact Or.inl hSuccess
  · right
    intro B
    have hEscape :
        ∃ n : Nat, ∀ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g →
          CofinalDiaryStageCompatible H m f g →
          B < g m := by
      by_contra hNone
      push_neg at hNone
      have hCover : FiniteHorizonNextLeafCover H K F m f := by
        refine ⟨Finset.range (B + 1),?_⟩
        intro n
        obtain ⟨g,hQ,hCompatible,hBound⟩ := hNone n
        refine ⟨g,hQ,hCompatible,?_⟩
        exact Finset.mem_range.mpr (by omega)
      obtain ⟨g,hNew,hCompatible⟩ :=
        exists_persistent_reserved_successor_of_finite_cover
          hm hCover
      exact hSuccess ⟨g,hNew,hCompatible⟩
    obtain ⟨n,hEvery⟩ := hEscape
    obtain ⟨g,hQ,hCompatible⟩ := P.2 (n + 1)
    have hEq : m + (n + 1) = m + 1 + n := by omega
    refine ⟨n,⟨g,by simpa only [hEq] using hQ,hCompatible⟩,hEvery⟩

end DiaryLeafPriority
end ThreeUniformDiaries
