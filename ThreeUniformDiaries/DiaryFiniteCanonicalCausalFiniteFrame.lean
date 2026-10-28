import ThreeUniformDiaries.DiaryFiniteCanonicalCausalPermittedEdges
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalSourceEdgeCensus

/-!
# Exact finite edge frame of the canonical causal sign-rooted graph

The completed graph is a Nat-indexed ternary relation, but the
finite pre-diary interface requires a frame whose edges are
supported within the ACTUAL finite carrier bound N. The first
three common source markers have ranks 0,1,2, so N >= 3.

Every edge of the raw indexed source union is supported within
N; its last source vertex is at least level three by the
source finite edge frame, hence its numerical rank is at least
three. Every newly inserted Devlin edge ends on a pair selected
by the geometric offbranch mask, whose ranks also belong to
the finite carrier and have last rank at least three.

The edge order has already been verified. This module packages
all of these literal finite support facts as a FiniteDiaryEdgeFrame.
It does not require the unproved output S1/S2 meets.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The actual canonical carrier contains at least the three
distinct numerical marker ranks 0, 1 and 2. -/
theorem finiteCanonicalCausalMarkerGraph_card_ge_three
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    3 ≤ Fintype.card (FiniteCanonicalSignRootedVertex DA) := by
  classical
  obtain ⟨i,_⟩ :=
    finiteCanonicalSignRootedFamily_complete
      DA (FiniteDiaryFlip.refl DA)
  have h2 : (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i 2 (by
        have hn := DA.prediary.frame.length_ge_three
        omega))).val = 2 :=
    finiteCanonicalMarker_two_rank DA i
  have hBound : (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i 2 (by
        have hn := DA.prediary.frame.length_ge_three
        omega))).val <
        Fintype.card (FiniteCanonicalSignRootedVertex DA) :=
    (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i 2 (by
        have hn := DA.prediary.frame.length_ge_three
        omega))).isLt
  omega

/-- Every edge of the completed causal graph has increasing
indices and last vertex within the actual finite carrier at
rank >= 3. This applies to both raw and new Devlin edges. -/
theorem finiteCanonicalCausalMarkerGraph_edge_support
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (x y z : Nat)
    (he : (finiteCanonicalCausalMarkerGraph DA).edge x y z) :
    x < y ∧ y < z ∧ 3 ≤ z ∧
      z < Fintype.card (FiniteCanonicalSignRootedVertex DA) := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let R := finiteCanonicalRankedRawGraph DA
  let M := finiteCanonicalRankedOffBranchMask DA
  have hOrder :=
    finiteCanonicalCausalMarkerGraph_edge_ordered DA x y z he
  have hFormula :=
    (causalMarkerLimit_formula R M
      (finiteCanonicalRankedOffBranchMask_later DA) x y z).mp he
  have hSupport : 3 ≤ z ∧
      z < Fintype.card (FiniteCanonicalSignRootedVertex DA) := by
    rcases hFormula with hRaw | ⟨_,hm,_⟩ | ⟨_,hm,_⟩
    · obtain ⟨i,a,b,c,hab,hbc,hX,hY,hZ,hSource⟩ :=
        finiteCanonicalRankedRawGraph_edge_source_witness
          DA x y z hRaw
      have hSrc3 : 3 ≤ c.val :=
        ((F.flip i).target_diary.prediary.frame.edge_support
          a.val b.val c.val hSource).2.2.1
      have hRank3 : 3 ≤
          (finiteCanonicalNodeIndex DA
            (finiteCanonicalNodeAt DA i c.val c.isLt)).val :=
        finiteCanonicalNodeAt_rank_ge_three
          DA i c.val hSrc3 c.isLt
      have hRankBound :
          (finiteCanonicalNodeIndex DA
            (finiteCanonicalNodeAt DA i c.val c.isLt)).val <
          Fintype.card (FiniteCanonicalSignRootedVertex DA) :=
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i c.val c.isLt)).isLt
      constructor
      · simpa only [hZ] using hRank3
      · simpa only [hZ] using hRankBound
    · obtain ⟨Y,Z,hY,hZ,hOff⟩ := hm
      have hyz := finiteCanonicalRankedOffBranchMask_supported
        DA y z ⟨Y,Z,hY,hZ,hOff⟩
      have hzBound := (finiteCanonicalNodeIndex DA Z).isLt
      constructor
      · omega
      · simpa only [hZ] using hzBound
    · obtain ⟨Y,Z,hY,hZ,hOff⟩ := hm
      have hyz := finiteCanonicalRankedOffBranchMask_supported
        DA y z ⟨Y,Z,hY,hZ,hOff⟩
      have hzBound := (finiteCanonicalNodeIndex DA Z).isLt
      constructor
      · omega
      · simpa only [hZ] using hzBound
  exact ⟨hOrder.1,hOrder.2.1,hSupport.1,hSupport.2⟩

/-- The EXACT finite edge frame of the causal canonical
sign-rooted graph, not just an abstract ordered edge set. -/
theorem finiteCanonicalCausalMarkerGraph_finiteFrame
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    FiniteDiaryEdgeFrame (finiteCanonicalCausalMarkerGraph DA)
      (Fintype.card (FiniteCanonicalSignRootedVertex DA)) := by
  exact ⟨finiteCanonicalCausalMarkerGraph_card_ge_three DA,
    finiteCanonicalCausalMarkerGraph_edge_support DA⟩

end DiaryLeafPriority
end ThreeUniformDiaries
