import ThreeUniformDiaries.DiaryFiniteCanonicalRankedOffBranchMask

/-!
# Instantiate literal causal V3 on the actual finite sign-rooted tree

Both required inputs now exist on Nat: the canonical sign-rooted
RAW relational graph and its genuine ranked off-branch mask.
Apply the separately checked causal marker fixed-point construction
to these two CONCRETE objects.

The resulting graph is a strictly ordered 3-hypergraph. Every
canonical genuine source flip remains an induced increasing branch
(its raw edges AND nonedges are untouched because the marker mask
never selects two vertices on one source branch). Every newly
ordered off-branch pair has EXACTLY the literal V3 marker-one and
marker-two orientation in the final graph; there is no guessed
prefix-uniform orientation or synthetic intermediate LexEarlier.

What remains: original branch V3 at the ACTUAL numbered raw meets,
the complete V1/V2 witnesses and other pre-diary role conditions,
mixed numerical-meet protection and general every-flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Actual ranked off-branch leaves have numerical index >=3.
The three common initial marker nodes precede every source leaf,
even before we establish their exact numerical ranks 0/1/2. -/
theorem finiteCanonicalRankedOffBranchMask_supported
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (y z : Nat)
    (hm : finiteCanonicalRankedOffBranchMask DA y z) :
    3 ≤ y ∧ y < z := by
  classical
  obtain ⟨Y,Z,hY,hZ,hOff⟩ := hm
  have hYsource : 3 ≤ Y.val.1 := hOff.leafY.1
  have hn : 3 ≤ n := DA.prediary.frame.length_ge_three
  obtain ⟨i,_⟩ := finiteCanonicalSignRootedFamily_complete
    DA (FiniteDiaryFlip.refl DA)
  have h01 :
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i 0 (by omega))).val <
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i 1 (by omega))).val :=
    finiteCanonicalNodeAt_index_lt DA i 0 1 (by omega) (by omega)
  have h12 :
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i 1 (by omega))).val <
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i 2 (by omega))).val :=
    finiteCanonicalNodeAt_index_lt DA i 1 2 (by omega) (by omega)
  have h2Y :
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i 2 (by omega))).val <
      (finiteCanonicalNodeIndex DA Y).val := by
    apply finiteCanonicalNodeIndex_lt_of_source_lt DA
    change 2 < Y.val.1
    omega
  have hy3 : 3 ≤ (finiteCanonicalNodeIndex DA Y).val := by
    omega
  constructor
  · rw [← hY]
    exact hy3
  · exact finiteCanonicalRankedOffBranchMask_later DA y z
      ⟨Y,Z,hY,hZ,hOff⟩

/-- No ranked RAW edge can end in a pair which the off-branch
mask selects: every original RAW edge belongs to some common
source flip branch, while the mask excludes such pairs. -/
theorem finiteCanonicalRankedRawGraph_no_edge_of_mask
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (x y z : Nat)
    (hm : finiteCanonicalRankedOffBranchMask DA y z) :
    ¬ (finiteCanonicalRankedRawGraph DA).edge x y z := by
  intro he
  obtain ⟨Y,Z,hY,hZ,hOff⟩ := hm
  obtain ⟨X',Y',Z',_,hY',hZ',hRaw⟩ := he
  have eY : Y' = Y := finiteCanonicalNodeIndex_injective DA
    (Fin.ext (hY'.trans hY.symm))
  have eZ : Z' = Z := finiteCanonicalNodeIndex_injective DA
    (Fin.ext (hZ'.trans hZ.symm))
  subst Y'
  subst Z'
  exact hOff.separated
    ((finiteCanonicalSignRootedFamily DA).
      raw_edge_implies_shared_branch_pair X'.val Y.val Z.val hRaw)

/-- The CONCRETE literal-V3 completed sign-rooted ternary graph
on the bounded, numerically enumerated finite canonical carrier. -/
noncomputable def finiteCanonicalCausalMarkerGraph
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) : Ordered3Graph Nat :=
  causalMarkerLimit (finiteCanonicalRankedRawGraph DA)
    (finiteCanonicalRankedOffBranchMask DA)

/-- Every new edge of the constructed graph is increasing in
the ACTUAL rank indices. -/
theorem finiteCanonicalCausalMarkerGraph_edge_ordered
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (x y z : Nat)
    (he : (finiteCanonicalCausalMarkerGraph DA).edge x y z) :
    x < y ∧ y < z := by
  exact causalMarkerLimit_edges_increasing
    (finiteCanonicalRankedRawGraph DA)
    (finiteCanonicalRankedOffBranchMask DA)
    (finiteCanonicalRankedRawGraph_edge_ordered DA)
    (finiteCanonicalRankedOffBranchMask_supported DA)
    x y z he

/-- Every canonical source flip branch survives the actual
causal V3 completion as an INDUCED and increasing copy,
including the nonedges of the finite source diary. -/
theorem finiteCanonicalCausalMarkerGraph_branch_edge_iff
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (x y z : Nat)
    (hxy : x < y) (hyz : y < z) (hzn : z < n) :
    (finiteCanonicalCausalMarkerGraph DA).edge
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i x (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i y (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i z hzn)).val ↔
    ((finiteCanonicalSignRootedFamily DA).graph i).edge x y z := by
  let a := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i x (by omega))).val
  let b := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i y (by omega))).val
  let c := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i z hzn)).val
  have hNoMask : ¬ finiteCanonicalRankedOffBranchMask DA b c :=
    finiteCanonicalRankedOffBranchMask_same_branch_false DA
      i y z hyz hzn
  have hFormula := causalMarkerLimit_formula
    (finiteCanonicalRankedRawGraph DA)
    (finiteCanonicalRankedOffBranchMask DA)
    (finiteCanonicalRankedOffBranchMask_later DA)
    a b c
  have hCopy :
      (finiteCanonicalCausalMarkerGraph DA).edge a b c ↔
        (finiteCanonicalRankedRawGraph DA).edge a b c := by
    simpa only [finiteCanonicalCausalMarkerGraph,
      CausalMarkerColumn, hNoMask, false_and,
      and_false, or_false] using hFormula
  exact hCopy.trans
    (finiteCanonicalRankedRawGraph_branch_edge_iff
      DA i x y z hxy hyz hzn)

/-- On each selected off-branch pair, the marker-one
incidence of the final concrete graph is its own
literal lexicographic comparison, not an approximation. -/
theorem finiteCanonicalCausalMarkerGraph_offbranch_marker_one
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (y z : Nat)
    (hm : finiteCanonicalRankedOffBranchMask DA y z) :
    (finiteCanonicalCausalMarkerGraph DA).edge 1 y z ↔
      LexEarlier (finiteCanonicalCausalMarkerGraph DA) y z := by
  exact causalMarkerLimit_marker_one
    (finiteCanonicalRankedRawGraph DA)
    (finiteCanonicalRankedOffBranchMask DA)
    (finiteCanonicalRankedOffBranchMask_later DA)
    y z hm (finiteCanonicalRankedRawGraph_no_edge_of_mask DA 1 y z hm)

/-- The other Devlin marker is exactly the complement,
again with the FINAL concrete graph's LexEarlier. -/
theorem finiteCanonicalCausalMarkerGraph_offbranch_marker_two
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (y z : Nat)
    (hm : finiteCanonicalRankedOffBranchMask DA y z) :
    (finiteCanonicalCausalMarkerGraph DA).edge 2 y z ↔
      ¬ LexEarlier (finiteCanonicalCausalMarkerGraph DA) y z := by
  exact causalMarkerLimit_marker_two
    (finiteCanonicalRankedRawGraph DA)
    (finiteCanonicalRankedOffBranchMask DA)
    (finiteCanonicalRankedOffBranchMask_later DA)
    y z hm (finiteCanonicalRankedRawGraph_no_edge_of_mask DA 2 y z hm)

end DiaryLeafPriority
end ThreeUniformDiaries
