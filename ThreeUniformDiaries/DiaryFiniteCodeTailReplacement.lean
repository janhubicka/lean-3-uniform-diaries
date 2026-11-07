import ThreeUniformDiaries.DiaryFiniteTailUnaryTypeCodes
import ThreeUniformDiaries.DiaryCanonicalTailTypeCone

/-!
# Relative reserved new-leaf replacement has an exact finite edge-bit code

At any already valid reserved new-leaf stage g0, the finite support
S_(m+1) yields an explicit canonical cut B one greater than the
largest image of any supported vertex OTHER than m.

A supplied later genuine outer-range target leaf v may replace
g0(m) if its finite set of mixed edge bits below B is identical
to the finite set for g0(m). This is exactly equality of complete
singleton types below B (including nonedges), not a stronger
hidden hypothesis.

The conclusion preserves all roles, induced triples/nontriples,
numeric S1/S2 meets, leaf range and future order reserve.

This is a DECIDABLE FINITE TABLE criterion for a SUPPLIED v,
not a theorem producing such a v or a countable coherent choice.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The full reserved-stage replacement theorem in the most
concrete finite-code form. The old support is fixed literally;
only the newly selected leaf m changes its target image. -/
theorem ReservedDiaryStage.replace_new_leaf_of_equal_finite_tail_code
    {H K : Ordered3Graph Nat} {F g0 : Nat → Nat}
    {m v : Nat}
    (hm : IsLeaf H m)
    (P : ReservedDiaryStage H K F (m + 1) g0)
    (hCode : tailOneTypeCode K
        (canonicalTailTypeCut H m g0) (g0 m) =
      tailOneTypeCode K
        (canonicalTailTypeCut H m g0) v)
    (hvLater : g0 m ≤ v)
    (hvLeaf : IsLeaf K v)
    (hvRange : ∃ t : Nat, v = F t) :
    ReservedDiaryStage H K F (m + 1)
      (replaceAt g0 m v) := by
  have hType : K.SameOneTypeBelow
      (canonicalTailTypeCut H m g0) (g0 m) v :=
    (tailOneTypeCode_eq_iff_sameOneTypeBelow
      K (canonicalTailTypeCut H m g0) (g0 m) v).mp hCode
  exact ReservedDiaryStage.replace_new_leaf_in_canonical_type_cone
    hm P hType hvLater hvLeaf hvRange

end DiaryLeafPriority
end ThreeUniformDiaries
