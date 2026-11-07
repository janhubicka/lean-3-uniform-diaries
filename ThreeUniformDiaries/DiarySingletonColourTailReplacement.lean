import ThreeUniformDiaries.DiaryFiniteSingletonColour
import ThreeUniformDiaries.DiaryCanonicalTailTypeCone

/-!
# Relative tail replacement directly from the EXISTING singleton mask

A valid reserved next-leaf image g0(m) can be replaced by a later
genuine target leaf v in the SAME prescribed F-range if the exact
finite Boolean singleton colours, already used for lower-bound
ATR stabilisation, agree below the canonical cut of g0's finite
support S_(m+1).

This reuses the pre-existing theorem
DiaryLowerBoundColors.singletonColour_eq_iff instead of introducing
a redundant second finite code.

The conclusion is the ENTIRE reserved stage, preserving markers,
roles, induced triples/nontriples, exact singleton/full pair meets,
leaf range and future order reserve. No existence of v or
countably persistent choice is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The full relative tail-cone replacement theorem in the
existing complete finite Boolean edge/nonedge-mask API. -/
theorem ReservedDiaryStage.replace_new_leaf_of_equal_singletonColour
    {H K : Ordered3Graph Nat} {F g0 : Nat → Nat}
    {m v : Nat}
    (hm : IsLeaf H m)
    (P : ReservedDiaryStage H K F (m + 1) g0)
    (hColour :
      DiaryLowerBoundColors.singletonColour K
        (canonicalTailTypeCut H m g0) (g0 m) =
      DiaryLowerBoundColors.singletonColour K
        (canonicalTailTypeCut H m g0) v)
    (hvLater : g0 m ≤ v)
    (hvLeaf : IsLeaf K v)
    (hvRange : ∃ t : Nat, v = F t) :
    ReservedDiaryStage H K F (m + 1)
      (replaceAt g0 m v) := by
  have hType : K.SameOneTypeBelow
      (canonicalTailTypeCut H m g0) (g0 m) v :=
    (DiaryLowerBoundColors.singletonColour_eq_iff
      K (canonicalTailTypeCut H m g0) (g0 m) v).mp hColour
  exact ReservedDiaryStage.replace_new_leaf_in_canonical_type_cone
    hm P hType hvLater hvLeaf hvRange


/-- If the PARTICULAR mixed singleton colour of a supplied valid
new-leaf image occurs at arbitrarily high target indices in the
original F-range, then it has arbitrarily high valid ONE-STEP
replacements fixing every other supported vertex.

This is a relative abundance theorem for immediate successors,
not a persistent successor theorem: a candidate may still fail
to admit a compatible continuation at a later source horizon. -/
theorem ReservedDiaryStage.exists_arbitrarily_late_new_leaf_in_type_cone
    {H K : Ordered3Graph Nat} {F g0 : Nat → Nat}
    {m : Nat}
    (hm : IsLeaf H m)
    (P : ReservedDiaryStage H K F (m + 1) g0)
    (hFleaf : ∀ t : Nat, IsLeaf K (F t))
    (hCone : ∀ M : Nat, ∃ t : Nat,
      M < F t ∧
      DiaryLowerBoundColors.singletonColour K
        (canonicalTailTypeCut H m g0) (F t) =
      DiaryLowerBoundColors.singletonColour K
        (canonicalTailTypeCut H m g0) (g0 m)) :
    ∀ M : Nat, ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1) g ∧
      (∀ u : Nat, u ∈ countableDiaryFiniteSupport H (m + 1) →
        u ≠ m → g u = g0 u) ∧ M < g m := by
  intro M
  obtain ⟨t,hHigh,hColour⟩ := hCone (max M (g0 m))
  have hLater : g0 m ≤ F t := by omega
  let g := replaceAt g0 m (F t)
  have hReserved : ReservedDiaryStage H K F (m + 1) g :=
    ReservedDiaryStage.replace_new_leaf_of_equal_singletonColour
      hm P hColour.symm hLater (hFleaf t) ⟨t,rfl⟩
  refine ⟨g,hReserved,?_,?_⟩
  · intro u _hu hNe
    exact replaceAt_other g0 m (F t) u hNe
  · have hM : M < F t := by omega
    simpa only [g,replaceAt_eq] using hM

end DiaryLeafPriority
end ThreeUniformDiaries
