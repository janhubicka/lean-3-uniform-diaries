import ThreeUniformDiaries.DiaryFiniteCanonicalSignRootedRank

/-!
# The actual canonical sign-rooted RAW relational union, indexed by Nat

The source-level-first order on the entire finite sign-rooted flip
carrier has an injective numerical rank into a finite initial
segment. Push the actual raw ternary relation forward along that
index, putting NO edges outside the finite realised carrier.

This produces a literal Ordered3Graph Nat, the input datatype
required by the causal Devlin marker fixed-point theorem.

Every genuine source flip branch is still embedded INDUCEDLY,
including all nonedges, at the exact rank indices of its original
source nodes. The indexed raw graph contains only increasing triples
and has no edges outside the bounded finite index interval.

The separate off-branch marker MASK will be transported to the same
indices next. No V3 completion or finite diary absorber is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A source vertex z<n on canonical flip branch i as an element
of the ACTUAL finite sign-rooted carrier. -/
noncomputable def finiteCanonicalNodeAt
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (z : Nat) (hzn : z < n) :
    FiniteCanonicalSignRootedVertex DA :=
  ⟨(finiteCanonicalSignRootedFamily DA).node i z,
    finiteCanonicalSignRootedNodeSet_contains DA i z hzn⟩

/-- Genuine bounded raw ternary relation with its vertices indexed
by the actual source-level-first finite canonical rank. -/
noncomputable def finiteCanonicalRankedRawGraph
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) : Ordered3Graph Nat where
  edge x y z :=
    ∃ X Y Z : FiniteCanonicalSignRootedVertex DA,
      (finiteCanonicalNodeIndex DA X).val = x ∧
      (finiteCanonicalNodeIndex DA Y).val = y ∧
      (finiteCanonicalNodeIndex DA Z).val = z ∧
      ((finiteCanonicalSignRootedFamily DA).rawAmalgam).edge
        X.val Y.val Z.val

/-- At three realised canonical nodes, the new ranked raw graph
has an edge IFF the original raw relational union has an edge. -/
theorem finiteCanonicalRankedRawGraph_edge_iff
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (X Y Z : FiniteCanonicalSignRootedVertex DA) :
    (finiteCanonicalRankedRawGraph DA).edge
      (finiteCanonicalNodeIndex DA X).val
      (finiteCanonicalNodeIndex DA Y).val
      (finiteCanonicalNodeIndex DA Z).val ↔
    ((finiteCanonicalSignRootedFamily DA).rawAmalgam).edge
      X.val Y.val Z.val := by
  constructor
  · rintro ⟨X',Y',Z',hX,hY,hZ,hEdge⟩
    have eX : X' = X := finiteCanonicalNodeIndex_injective DA (Fin.ext hX)
    have eY : Y' = Y := finiteCanonicalNodeIndex_injective DA (Fin.ext hY)
    have eZ : Z' = Z := finiteCanonicalNodeIndex_injective DA (Fin.ext hZ)
    subst X'
    subst Y'
    subst Z'
    exact hEdge
  · intro h
    exact ⟨X,Y,Z,rfl,rfl,rfl,h⟩

/-- Along one canonical branch, the rank indices are strictly
increasing in the original source vertex order. -/
theorem finiteCanonicalNodeAt_index_lt
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (x y : Nat) (hxy : x < y) (hyn : y < n) :
    (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i x (by omega))).val <
    (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i y hyn)).val := by
  apply finiteCanonicalNodeIndex_lt_of_source_lt DA
  simpa only [finiteCanonicalNodeAt,
    FiniteSignRootedFlipFamily.node_level] using hxy

/-- Every original genuine source flip branch remains a FULL
induced copy of its own three-hypergraph in the ranked Nat graph. -/
theorem finiteCanonicalRankedRawGraph_branch_edge_iff
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (x y z : Nat)
    (hxy : x < y) (hyz : y < z) (hzn : z < n) :
    (finiteCanonicalRankedRawGraph DA).edge
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i x (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i y (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i z hzn)).val ↔
      ((finiteCanonicalSignRootedFamily DA).graph i).edge x y z := by
  have hRank := finiteCanonicalRankedRawGraph_edge_iff DA
    (finiteCanonicalNodeAt DA i x (by omega))
    (finiteCanonicalNodeAt DA i y (by omega))
    (finiteCanonicalNodeAt DA i z hzn)
  have hRaw := (finiteCanonicalSignRootedFamily DA).rawAmalgam_edge_iff
    i x y z hxy hyz hzn
  simpa only [finiteCanonicalNodeAt] using hRank.trans hRaw

/-- Every ranked raw edge is supported on a STRICTLY increasing
triple of numerical vertices, not merely a triple of unequal nodes. -/
theorem finiteCanonicalRankedRawGraph_edge_ordered
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (x y z : Nat)
    (h : (finiteCanonicalRankedRawGraph DA).edge x y z) :
    x < y ∧ y < z := by
  obtain ⟨X,Y,Z,hX,hY,hZ,hRaw⟩ := h
  obtain ⟨i,a,b,c,hab,hbc,hcn,ha,hb,hc,_⟩ := hRaw
  have hLa : X.val.1 = a := by
    simpa only [FiniteSignRootedFlipFamily.node_level] using
      (congrArg Prod.fst ha.symm)
  have hLb : Y.val.1 = b := by
    simpa only [FiniteSignRootedFlipFamily.node_level] using
      (congrArg Prod.fst hb.symm)
  have hLc : Z.val.1 = c := by
    simpa only [FiniteSignRootedFlipFamily.node_level] using
      (congrArg Prod.fst hc.symm)
  have hXY := finiteCanonicalNodeIndex_lt_of_source_lt
    DA X Y (by omega)
  have hYZ := finiteCanonicalNodeIndex_lt_of_source_lt
    DA Y Z (by omega)
  constructor
  · simpa only [hX,hY] using hXY
  · simpa only [hY,hZ] using hYZ

/-- No raw edge can involve any index outside the ACTUAL
finite carrier's consecutive numerical range. -/
theorem finiteCanonicalRankedRawGraph_edge_bounded
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (x y z : Nat)
    (h : (finiteCanonicalRankedRawGraph DA).edge x y z) :
    x < Fintype.card (FiniteCanonicalSignRootedVertex DA) ∧
    y < Fintype.card (FiniteCanonicalSignRootedVertex DA) ∧
    z < Fintype.card (FiniteCanonicalSignRootedVertex DA) := by
  obtain ⟨X,Y,Z,hX,hY,hZ,_⟩ := h
  have bX := (finiteCanonicalNodeIndex DA X).isLt
  have bY := (finiteCanonicalNodeIndex DA Y).isLt
  have bZ := (finiteCanonicalNodeIndex DA Z).isLt
  rw [hX] at bX
  rw [hY] at bY
  rw [hZ] at bZ
  exact ⟨bX,bY,bZ⟩

end DiaryLeafPriority
end ThreeUniformDiaries
