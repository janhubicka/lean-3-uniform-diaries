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

end DiaryLeafPriority
end ThreeUniformDiaries
