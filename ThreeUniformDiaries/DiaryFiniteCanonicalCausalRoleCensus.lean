import ThreeUniformDiaries.DiaryFiniteCanonicalCausalOriginalV3
import ThreeUniformDiaries.DiaryFiniteCanonicalExactMarkerRanks
import ThreeUniformDiaries.DiaryFiniteCanonicalRankedOffBranchMask

/-!
# Complete finite vertex census and marker-defined roles of the causal graph

The causal marker extension has now been proved to preserve all original
branch triples inducedly, and the three distinguished source markers
have EXACT target ranks 0,1,2.

Therefore every realised raw source vertex has precisely the same
role-marker incidences (0,1,z)/(0,2,z) in the completed causal graph.
At original levels >=3, the final numerical rank is also >=3.
Thus all three marker-defined roles (leaf, 1-split, 2-split) are
preserved and reflected, despite the extra nodes and ties.

Every actual finite target vertex is the rank of a node on some
canonical source-flip branch, by the literal finite carrier image.
The resulting role census gives full bounded role coverage. In
particular every completed-graph leaf comes from a genuine source
leaf of some original branch. No V1/V2 witnesses or S-meet
properties of the completed graph are asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The three marker-defined roles are transported by any
pair of exact role-marker incidence equivalences together
with both lower bounds on the vertex indices. -/
theorem marker_roles_iff_of_role_bits
    (H K : Ordered3Graph Nat)
    (x y : Nat) (hx : 3 ≤ x) (hy : 3 ≤ y)
    (h01 : H.edge 0 1 x ↔ K.edge 0 1 y)
    (h02 : H.edge 0 2 x ↔ K.edge 0 2 y) :
    (IsLeaf H x ↔ IsLeaf K y) ∧
    (IsOneSplit H x ↔ IsOneSplit K y) ∧
    (IsTwoSplit H x ↔ IsTwoSplit K y) := by
  constructor
  · simp [IsLeaf,hx,hy,h01,h02]
  constructor
  · simp [IsOneSplit,hx,hy,h01,h02]
  · simp [IsTwoSplit,hx,hy,h01,h02]

/-- Source marker levels below three have their EXACT original
numerical rank. This is the small-marker form of PR #904. -/
theorem finiteCanonicalMarker_index_of_lt_three
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (z : Nat) (hz : z < 3) (hzn : z < n) :
    (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i z hzn)).val = z := by
  interval_cases z
  · exact finiteCanonicalMarker_zero_rank DA i
  · exact finiteCanonicalMarker_one_rank DA i
  · exact finiteCanonicalMarker_two_rank DA i

/-- Every source non-marker vertex at level z>=3 is also at
numerical rank >=3 in the entire canonical sign-rooted carrier. -/
theorem finiteCanonicalNodeAt_rank_ge_three
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (z : Nat) (hz : 3 ≤ z) (hzn : z < n) :
    3 ≤ (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i z hzn)).val := by
  have hn : 3 ≤ n := DA.prediary.frame.length_ge_three
  have h2z := finiteCanonicalNodeAt_index_lt
    DA i 2 z (by omega) hzn
  have hMarker2 : (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i 2 (by omega))).val = 2 :=
    finiteCanonicalMarker_two_rank DA i
  omega

/-- Exact final-graph reflection of both role-marker edges
(0,1,z) and (0,2,z) on an arbitrary canonical source branch. -/
theorem finiteCanonicalCausalMarkerGraph_branch_role_bits
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (z : Nat) (hz : 3 ≤ z) (hzn : z < n) :
    ((finiteCanonicalCausalMarkerGraph DA).edge 0 1
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i z hzn)).val ↔
      ((finiteCanonicalSignRootedFamily DA).graph i).edge 0 1 z) ∧
    ((finiteCanonicalCausalMarkerGraph DA).edge 0 2
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i z hzn)).val ↔
      ((finiteCanonicalSignRootedFamily DA).graph i).edge 0 2 z) := by
  have hn : 3 ≤ n := DA.prediary.frame.length_ge_three
  have hMark0 : (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i 0 (by omega))).val = 0 :=
    finiteCanonicalMarker_zero_rank DA i
  have hMark1 : (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i 1 (by omega))).val = 1 :=
    finiteCanonicalMarker_one_rank DA i
  have hMark2 : (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i 2 (by omega))).val = 2 :=
    finiteCanonicalMarker_two_rank DA i
  constructor
  · have h := finiteCanonicalCausalMarkerGraph_branch_edge_iff
      DA i 0 1 z (by omega) (by omega) hzn
    simpa only [hMark0,hMark1] using h
  · have h := finiteCanonicalCausalMarkerGraph_branch_edge_iff
      DA i 0 2 z (by omega) (by omega) hzn
    simpa only [hMark0,hMark2] using h

/-- All three ACTUAL completed-graph roles at a genuine source
vertex are precisely the original source diary's roles. The
result is independent of which canonical flip presents the node. -/
theorem finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (z : Nat) (hz : 3 ≤ z) (hzn : z < n) :
    (IsLeaf (finiteCanonicalCausalMarkerGraph DA)
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i z hzn)).val ↔ IsLeaf A z) ∧
    (IsOneSplit (finiteCanonicalCausalMarkerGraph DA)
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i z hzn)).val ↔ IsOneSplit A z) ∧
    (IsTwoSplit (finiteCanonicalCausalMarkerGraph DA)
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i z hzn)).val ↔ IsTwoSplit A z) := by
  let F := finiteCanonicalSignRootedFamily DA
  let k := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i z hzn)).val
  have hk3 : 3 ≤ k :=
    finiteCanonicalNodeAt_rank_ge_three DA i z hz hzn
  have hBits := finiteCanonicalCausalMarkerGraph_branch_role_bits
    DA i z hz hzn
  have hRoles := marker_roles_iff_of_role_bits
    (finiteCanonicalCausalMarkerGraph DA)
    (F.graph i) k z hk3 hz hBits.1 hBits.2
  have hFlip := (F.flip i).role_iff z hz hzn
  exact ⟨hRoles.1.trans hFlip.1.symm,
    hRoles.2.1.trans hFlip.2.1.symm,
    hRoles.2.2.trans hFlip.2.2.symm⟩

/-- Every valid numerical index in the actual canonical finite
carrier is represented by a vertex of some original flip branch,
even though many branch vertices are shared. -/
theorem finiteCanonicalNodeIndex_census
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (k : Nat)
    (hk : k < Fintype.card (FiniteCanonicalSignRootedVertex DA)) :
    ∃ (i : FiniteCanonicalFlipIndex A n) (z : Nat) (hzn : z < n),
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i z hzn)).val = k := by
  classical
  obtain ⟨X,hX⟩ := finiteCanonicalNodeIndex_surjective DA
    (⟨k,hk⟩ : Fin (Fintype.card (FiniteCanonicalSignRootedVertex DA)))
  have hMember : X.val ∈ finiteCanonicalSignRootedNodeSet DA :=
    X.property
  unfold finiteCanonicalSignRootedNodeSet at hMember
  obtain ⟨⟨i,z⟩,_,hImage⟩ := Finset.mem_image.mp hMember
  refine ⟨i,z.val,z.isLt,?_⟩
  have hSubtype : X = finiteCanonicalNodeAt DA i z.val z.isLt := by
    apply Subtype.ext
    exact hImage.symm
  have hXval : (finiteCanonicalNodeIndex DA X).val = k :=
    congrArg Fin.val hX
  simpa only [← hSubtype] using hXval

/-- Every true completed-graph leaf within the finite carrier is
the numerical image of a TRUE source leaf in some original
canonical source-flip branch. -/
theorem finiteCanonicalCausalMarkerGraph_leaf_census
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (k : Nat)
    (hBound : k < Fintype.card (FiniteCanonicalSignRootedVertex DA))
    (hk : IsLeaf (finiteCanonicalCausalMarkerGraph DA) k) :
    ∃ (i : FiniteCanonicalFlipIndex A n) (z : Nat)
        (hzn : z < n),
      IsLeaf A z ∧
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i z hzn)).val = k := by
  obtain ⟨i,z,hzn,hIndex⟩ := finiteCanonicalNodeIndex_census DA k hBound
  have hz3 : 3 ≤ z := by
    by_contra h
    have hzSmall : z < 3 := by omega
    have hRank := finiteCanonicalMarker_index_of_lt_three
      DA i z hzSmall hzn
    omega
  have hRoles := finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
    DA i z hz3 hzn
  have hLeafImage : IsLeaf (finiteCanonicalCausalMarkerGraph DA)
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i z hzn)).val := by
    simpa only [hIndex] using hk
  exact ⟨i,z,hzn,hRoles.1.mp hLeafImage,hIndex⟩

/-- The completed graph has the full bounded V-role COVERAGE
condition on every finite carrier vertex, without postulating
a completed pre-diary. V1/V2 coherence and witness clauses
remain separate obligations. -/
theorem finiteCanonicalCausalMarkerGraph_role_valid
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (k : Nat) (hk3 : 3 ≤ k)
    (hk : k < Fintype.card (FiniteCanonicalSignRootedVertex DA)) :
    IsLeaf (finiteCanonicalCausalMarkerGraph DA) k ∨
    IsOneSplit (finiteCanonicalCausalMarkerGraph DA) k ∨
    IsTwoSplit (finiteCanonicalCausalMarkerGraph DA) k := by
  obtain ⟨i,z,hzn,hIndex⟩ := finiteCanonicalNodeIndex_census DA k hk
  have hz3 : 3 ≤ z := by
    by_contra h
    have hzSmall : z < 3 := by omega
    have hRank := finiteCanonicalMarker_index_of_lt_three
      DA i z hzSmall hzn
    omega
  have hRole := DA.prediary.role_valid z hz3 hzn
  have hIff := finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
    DA i z hz3 hzn
  rcases hRole with hLeaf | hOne | hTwo
  · exact Or.inl (by
      simpa only [hIndex] using (hIff.1.mpr hLeaf))
  · exact Or.inr (Or.inl (by
      simpa only [hIndex] using (hIff.2.1.mpr hOne)))
  · exact Or.inr (Or.inr (by
      simpa only [hIndex] using (hIff.2.2.mpr hTwo)))

end DiaryLeafPriority
end ThreeUniformDiaries
