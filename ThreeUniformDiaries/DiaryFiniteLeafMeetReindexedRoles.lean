import ThreeUniformDiaries.DiaryFiniteLeafMeetMarkerReindex
import ThreeUniformDiaries.DiaryFiniteLeafMeetRoleSupport

/-!
# Exhaustive genuine marker roles in the finite leaf-meet reduct

The source is a countable RoleDiary and L is a finite set of
its genuine leaves. Every selected vertex of the leaf-meet
support is a marker, a selected leaf, a singleton one-meet
(one-split), or an ordered-pair full two-meet (marker one,
a capped selected leaf, or a two-split).

The finite increasing support index maps genuine finite
nonmarker indices to old nonmarker vertices and reflects the
marker-defined role predicates. Thus every finite nonmarker
vertex of the induced reindexed graph has exactly one of the
three permitted diary roles. No S1/S2 or V1/V2 witness
preservation is asserted by this role lemma alone.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {G : Ordered3Graph Nat} {L : Finset Nat}

/-- Complete bounded role coverage of the actual reindexed
induced finite leaf-meet support. -/
theorem finiteLeafMeetSupport_reindexed_role_valid
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    (z : Nat)
    (hz3 : 3 ≤ z)
    (hzBound : z < (finiteLeafMeetSupport G L).card) :
    IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) z ∨
      IsOneSplit (finiteSupportGraph G (finiteLeafMeetSupport G L)) z ∨
      IsTwoSplit (finiteSupportGraph G (finiteLeafMeetSupport G L)) z := by
  let S := finiteLeafMeetSupport G L
  have h0 : 0 ∈ S := mem_finiteLeafMeetSupport_marker G L 0 (by omega)
  have h1 : 1 ∈ S := mem_finiteLeafMeetSupport_marker G L 1 (by omega)
  have h2 : 2 ∈ S := mem_finiteLeafMeetSupport_marker G L 2 (by omega)
  have hMem : finiteSupportIndex S z ∈ S :=
    finiteSupportIndex_mem S z hzBound
  have hOldGe : 3 ≤ finiteSupportIndex S z :=
    le_trans hz3 (finiteSupportIndex_ge_index S z hzBound)
  rcases finiteLeafMeetSupport_role D hLeaves hMem with
      hMarker | hLeaf | hOne | hTwo
  · omega
  · exact Or.inl
      ((finiteSupportGraph_leaf_iff
        (G := G) (S := S) h0 h1 h2 z hz3 hzBound).mpr hLeaf)
  · exact Or.inr (Or.inl
      ((finiteSupportGraph_oneSplit_iff
        (G := G) (S := S) h0 h1 h2 z hz3 hzBound).mpr hOne))
  · exact Or.inr (Or.inr
      ((finiteSupportGraph_twoSplit_iff
        (G := G) (S := S) h0 h1 h2 z hz3 hzBound).mpr hTwo))

end DiaryLeafPriority
end ThreeUniformDiaries
