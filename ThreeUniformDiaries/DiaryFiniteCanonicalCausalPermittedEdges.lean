import ThreeUniformDiaries.DiaryFiniteCanonicalCausalEdgeShapeRoles
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalSourceEdgeCensus

/-!
# All five permitted edge forms of the concrete causal sign-rooted graph

The completed graph is the union of the genuine canonical source
flip edge tables and the new literal causal Devlin marker incidences.
Every RAW edge has an actual bounded source-branch witness. Its
source finite diary has one of the five permitted E-shapes, and the
ranked completion preserves the three marker positions and all
marker-defined roles. Each of the five alternatives therefore
transports to the numerical completed graph.

Every NEW edge has first vertex marker 1 or marker 2 and its last
two vertices form an actual masked pair. The verified masked-pair
role transport proves they are completed-graph leaves, so these
edges have the permitted Devlin E4 shape.

This establishes the COMPLETE permitted-edge field needed by the
finite pre-diary on the actual concrete causal graph, with no
pre-diary assumption on the output.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every actual finite causal edge belongs to one of the
five manuscript permitted edge forms E1--E5. -/
theorem finiteCanonicalCausalMarkerGraph_permitted_edge
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (x y z : Nat)
    (he : (finiteCanonicalCausalMarkerGraph DA).edge x y z) :
    PermittedDiaryEdge (finiteCanonicalCausalMarkerGraph DA)
      x y z := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let G := finiteCanonicalCausalMarkerGraph DA
  let R := finiteCanonicalRankedRawGraph DA
  let M := finiteCanonicalRankedOffBranchMask DA
  have hCases :
      R.edge x y z ∨
      (x = 1 ∧ M y z ∧ LexEarlier G y z) ∨
      (x = 2 ∧ M y z ∧ ¬ LexEarlier G y z) := by
    have h := (causalMarkerLimit_formula R M
      (finiteCanonicalRankedOffBranchMask_later DA)
      x y z).mp he
    exact h
  rcases hCases with hRaw | hDev1 | hDev2
  · obtain ⟨i,a,b,c,hab,hbc,hX,hY,hZ,hEdge⟩ :=
      finiteCanonicalRankedRawGraph_edge_source_witness
        DA x y z hRaw
    have hSmall (t : Fin n) (ht : t.val < 3) :
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i t.val t.isLt)).val =
        t.val :=
      finiteCanonicalMarker_index_of_lt_three
        DA i t.val ht t.isLt
    have hLeaf (t : Fin n)
        (ht : IsLeaf (F.graph i) t.val) :
        IsLeaf G (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i t.val t.isLt)).val :=
      (finiteCanonicalCausalMarkerGraph_flip_role_transport
        DA i t ht.1).1.mp ht
    have hOne (t : Fin n)
        (ht : IsOneSplit (F.graph i) t.val) :
        IsOneSplit G (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i t.val t.isLt)).val :=
      (finiteCanonicalCausalMarkerGraph_flip_role_transport
        DA i t ht.1).2.1.mp ht
    have hTwo (t : Fin n)
        (ht : IsTwoSplit (F.graph i) t.val) :
        IsTwoSplit G (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i t.val t.isLt)).val :=
      (finiteCanonicalCausalMarkerGraph_flip_role_transport
        DA i t ht.1).2.2.mp ht
    have hPerm := (F.flip i).target_diary.prediary.permitted_edge
      a.val b.val c.val hEdge
    rcases hPerm with hE1 | hE2 | hE3 | hE4 | hE5
    · obtain ⟨ha0,hbMark,hc3⟩ := hE1
      have hx0 : x = 0 := by
        have hr := hSmall a (by omega)
        omega
      have hyMark : y = 1 ∨ y = 2 := by
        have hr := hSmall b (by omega)
        rcases hbMark with hb1 | hb2
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      have hz3 : 3 ≤ z := by
        have hr := finiteCanonicalNodeAt_rank_ge_three
          DA i c.val hc3 c.isLt
        omega
      exact Or.inl ⟨hx0,hyMark,hz3⟩
    · obtain ⟨ha0,hbOne,hcLeaf⟩ := hE2
      have hx0 : x = 0 := by
        have hr := hSmall a (by omega)
        omega
      have hyOne : IsOneSplit G y := by
        have hr := hOne b hbOne
        simpa only [hY] using hr
      have hzLeaf : IsLeaf G z := by
        have hr := hLeaf c hcLeaf
        simpa only [hZ] using hr
      exact Or.inr (Or.inl ⟨hx0,hyOne,hzLeaf⟩)
    · obtain ⟨haTwo,hbLeaf,hcLeaf⟩ := hE3
      have hxTwo : IsTwoSplit G x := by
        have hr := hTwo a haTwo
        simpa only [hX] using hr
      have hyLeaf : IsLeaf G y := by
        have hr := hLeaf b hbLeaf
        simpa only [hY] using hr
      have hzLeaf : IsLeaf G z := by
        have hr := hLeaf c hcLeaf
        simpa only [hZ] using hr
      exact Or.inr (Or.inr (Or.inl ⟨hxTwo,hyLeaf,hzLeaf⟩))
    · obtain ⟨haMark,hbLeaf,hcLeaf⟩ := hE4
      have hxDev : x = 1 ∨ x = 2 := by
        have hr := hSmall a (by omega)
        rcases haMark with ha1 | ha2
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      have hyLeaf : IsLeaf G y := by
        have hr := hLeaf b hbLeaf
        simpa only [hY] using hr
      have hzLeaf : IsLeaf G z := by
        have hr := hLeaf c hcLeaf
        simpa only [hZ] using hr
      exact Or.inr (Or.inr (Or.inr
        (Or.inl ⟨hxDev,hyLeaf,hzLeaf⟩)))
    · obtain ⟨haLeaf,hbLeaf,hcLeaf⟩ := hE5
      have hxLeaf : IsLeaf G x := by
        have hr := hLeaf a haLeaf
        simpa only [hX] using hr
      have hyLeaf : IsLeaf G y := by
        have hr := hLeaf b hbLeaf
        simpa only [hY] using hr
      have hzLeaf : IsLeaf G z := by
        have hr := hLeaf c hcLeaf
        simpa only [hZ] using hr
      exact Or.inr (Or.inr (Or.inr
        (Or.inr ⟨hxLeaf,hyLeaf,hzLeaf⟩)))
  · obtain ⟨hx,hm,_⟩ := hDev1
    have hLeaves :=
      finiteCanonicalCausalMarkerGraph_masked_pair_leaves
        DA y z hm
    exact Or.inr (Or.inr (Or.inr
      (Or.inl ⟨Or.inl hx,hLeaves.1,hLeaves.2⟩)))
  · obtain ⟨hx,hm,_⟩ := hDev2
    have hLeaves :=
      finiteCanonicalCausalMarkerGraph_masked_pair_leaves
        DA y z hm
    exact Or.inr (Or.inr (Or.inr
      (Or.inl ⟨Or.inr hx,hLeaves.1,hLeaves.2⟩)))

end DiaryLeafPriority
end ThreeUniformDiaries
