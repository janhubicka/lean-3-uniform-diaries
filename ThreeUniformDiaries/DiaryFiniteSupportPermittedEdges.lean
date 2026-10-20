import ThreeUniformDiaries.DiaryFiniteLeafMeetS1Reduct
import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface

/-!
# Finite induced restrictions preserve E1--E5 and the edge frame

A finite increasing induced restriction of a genuine RoleDiary,
provided all three marker vertices are retained, has:
* the correct bound on every positive edge;
* the same five permitted kinds of edge, with roles determined
  by the actual reindexed marker incidences.

This does NOT assert the finite V-witnesses, V3, or S1/S2. It is
valid for arbitrary finite supports containing the markers,
not only for a leaf-meet closed support.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {G : Ordered3Graph Nat} {S : Finset Nat}

/-- Any selected old marker below 3 is at its original index in an
increasing finite support which contains the three markers. -/
theorem finiteSupportIndex_fixed_of_image_lt_three
    (S : Finset Nat)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S)
    (i : Nat) (hi : i < S.card)
    (hOld : finiteSupportIndex S i < 3) :
    finiteSupportIndex S i = i := by
  obtain ⟨_,hZero,hOne,hTwo⟩ :=
    finiteSupportIndex_initial_markers S h0 h1 h2
  have hSmall : i < 3 := by
    have hge := finiteSupportIndex_ge_index S i hi
    omega
  interval_cases i
  · exact hZero
  · exact hOne
  · exact hTwo

/-- All E1--E5 shapes are inherited by ANY increasing induced
finite support containing the three distinguished markers. -/
theorem finiteSupportGraph_permitted_edge
    (D : RoleDiary G)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S)
    (x y z : Nat)
    (he : (finiteSupportGraph G S).edge x y z) :
    PermittedDiaryEdge (finiteSupportGraph G S) x y z := by
  have hOrdered := finiteSupportGraph_edge_ordered G S x y z he
  obtain ⟨hxy,hyz,hz⟩ := hOrdered
  have hx : x < S.card := by omega
  have hy : y < S.card := by omega
  have hOldEdge :
      G.edge (finiteSupportIndex S x)
        (finiteSupportIndex S y) (finiteSupportIndex S z) :=
    (finiteSupportGraph_edge_iff G S x y z hxy hyz hz).mp he
  have hLeaf : ∀ i : Nat, i < S.card →
      IsLeaf G (finiteSupportIndex S i) →
        IsLeaf (finiteSupportGraph G S) i := by
    intro i hi hiLeaf
    have hi3 := finiteSupportIndex_ge_three_of_image
      S i h0 h1 h2 hi hiLeaf.1
    exact (finiteSupportGraph_leaf_iff
      (G := G) (S := S) h0 h1 h2 i hi3 hi).mpr hiLeaf
  have hOne : ∀ i : Nat, i < S.card →
      IsOneSplit G (finiteSupportIndex S i) →
        IsOneSplit (finiteSupportGraph G S) i := by
    intro i hi hiOne
    have hi3 := finiteSupportIndex_ge_three_of_image
      S i h0 h1 h2 hi hiOne.1
    exact (finiteSupportGraph_oneSplit_iff
      (G := G) (S := S) h0 h1 h2 i hi3 hi).mpr hiOne
  have hTwo : ∀ i : Nat, i < S.card →
      IsTwoSplit G (finiteSupportIndex S i) →
        IsTwoSplit (finiteSupportGraph G S) i := by
    intro i hi hiTwo
    have hi3 := finiteSupportIndex_ge_three_of_image
      S i h0 h1 h2 hi hiTwo.1
    exact (finiteSupportGraph_twoSplit_iff
      (G := G) (S := S) h0 h1 h2 i hi3 hi).mpr hiTwo
  rcases D.permitted_edge _ _ _ hOldEdge with
      hMarker | hSplit | hPair | hDevlin | hNormal
  · obtain ⟨hxOld,hyOld,hzOld⟩ := hMarker
    have hxFixed := finiteSupportIndex_fixed_of_image_lt_three
      S h0 h1 h2 x hx (by omega)
    have hyFixed := finiteSupportIndex_fixed_of_image_lt_three
      S h0 h1 h2 y hy (by omega)
    have hzNew := finiteSupportIndex_ge_three_of_image
      S z h0 h1 h2 hz hzOld
    left
    refine ⟨?_, ?_, hzNew⟩
    · omega
    · rcases hyOld with hh | hh <;> omega
  · obtain ⟨hxOld,hyOne,hzLeaf⟩ := hSplit
    have hxFixed := finiteSupportIndex_fixed_of_image_lt_three
      S h0 h1 h2 x hx (by omega)
    right
    left
    refine ⟨?_, hOne y hy hyOne, hLeaf z hz hzLeaf⟩
    omega
  · obtain ⟨hxTwo,hyLeaf,hzLeaf⟩ := hPair
    right
    right
    left
    exact ⟨hTwo x hx hxTwo, hLeaf y hy hyLeaf, hLeaf z hz hzLeaf⟩
  · obtain ⟨hxOld,hyLeaf,hzLeaf⟩ := hDevlin
    have hxFixed := finiteSupportIndex_fixed_of_image_lt_three
      S h0 h1 h2 x hx (by omega)
    right
    right
    right
    left
    refine ⟨?_, hLeaf y hy hyLeaf, hLeaf z hz hzLeaf⟩
    rcases hxOld with hh | hh <;> omega
  · obtain ⟨hxLeaf,hyLeaf,hzLeaf⟩ := hNormal
    right
    right
    right
    right
    exact ⟨hLeaf x hx hxLeaf, hLeaf y hy hyLeaf, hLeaf z hz hzLeaf⟩

/-- The arbitrary induced finite support of a countable diary is
an honest bounded edge frame; in particular no positive edge
can end at one of the three markers. -/
theorem finiteSupportGraph_finiteEdgeFrame
    (D : RoleDiary G)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S) :
    FiniteDiaryEdgeFrame (finiteSupportGraph G S) S.card := by
  refine ⟨(finiteSupportIndex_initial_markers S h0 h1 h2).1, ?_⟩
  intro a b c he
  obtain ⟨hab,hbc,hc⟩ :=
    finiteSupportGraph_edge_ordered G S a b c he
  have hp := finiteSupportGraph_permitted_edge D h0 h1 h2 a b c he
  have hc3 : 3 ≤ c := by
    rcases hp with hMarker | hSplit | hPair | hDevlin | hNormal
    · exact hMarker.2.2
    · exact hSplit.2.2.1
    · exact hPair.2.2.1
    · exact hDevlin.2.2.1
    · exact hNormal.2.2.1
  exact ⟨hab,hbc,hc3,hc⟩

end DiaryLeafPriority
end ThreeUniformDiaries
