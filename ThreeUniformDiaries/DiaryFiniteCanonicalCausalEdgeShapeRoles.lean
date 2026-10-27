import ThreeUniformDiaries.DiaryFiniteCanonicalCausalSourceEdgeCensus
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalRoleCensus

/-!
# Finite source-role and off-branch mask endpoint transport

The five permitted diary edge forms refer to the actual marker-defined
roles of their vertices. For an original canonical source-flip branch,
the completed causal graph preserves both role-marker bits and their
literal positions 0,1,2.

For new Devlin marker edges, the geometric mask selects exactly two
source leaves. We verify that any finite masked pair consists of TRUE
leaves of the completed causal graph, not merely nodes described as
leaves in the raw source representation.

These two lemmas are the reusable edge-shape inputs. The complete
E1--E5 permitted-edge proof is the subsequent assembly step.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The three marker-defined roles of each original source-flip
vertex agree exactly with those of its actual ranked image in
the completed causal graph. -/
theorem finiteCanonicalCausalMarkerGraph_flip_role_transport
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (z : Fin n) (hz : 3 ≤ z.val) :
    (IsLeaf ((finiteCanonicalSignRootedFamily DA).graph i) z.val ↔
      IsLeaf (finiteCanonicalCausalMarkerGraph DA)
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i z.val z.isLt)).val) ∧
    (IsOneSplit ((finiteCanonicalSignRootedFamily DA).graph i) z.val ↔
      IsOneSplit (finiteCanonicalCausalMarkerGraph DA)
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i z.val z.isLt)).val) ∧
    (IsTwoSplit ((finiteCanonicalSignRootedFamily DA).graph i) z.val ↔
      IsTwoSplit (finiteCanonicalCausalMarkerGraph DA)
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i z.val z.isLt)).val) := by
  let F := finiteCanonicalSignRootedFamily DA
  have hFlip := (F.flip i).role_iff z.val hz z.isLt
  have hFinal :=
    finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
      DA i z.val hz z.isLt
  exact ⟨hFlip.1.symm.trans hFinal.1.symm,
    hFlip.2.1.symm.trans hFinal.2.1.symm,
    hFlip.2.2.symm.trans hFinal.2.2.symm⟩

/-- Each realised source node of original leaf role is a
TRUE leaf at its numerical rank in the final causal graph.
The source node may lie on multiple canonical flip branches. -/
theorem finiteCanonicalCausalMarkerGraph_leaf_at_rank
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (X : FiniteCanonicalSignRootedVertex DA)
    (hX : IsLeaf A X.val.1) :
    IsLeaf (finiteCanonicalCausalMarkerGraph DA)
      (finiteCanonicalNodeIndex DA X).val := by
  classical
  obtain ⟨i,z,hzn,hRank⟩ :=
    finiteCanonicalNodeIndex_census
      DA (finiteCanonicalNodeIndex DA X).val
        (finiteCanonicalNodeIndex DA X).isLt
  have hSame : X = finiteCanonicalNodeAt DA i z hzn := by
    apply finiteCanonicalNodeIndex_injective DA
    exact Fin.ext hRank.symm
  have hLevel : X.val.1 = z := by
    have h := congrArg
      (fun Y : FiniteCanonicalSignRootedVertex DA => Y.val.1)
      hSame
    simpa only [finiteCanonicalNodeAt_level] using h
  have hLeafSource : IsLeaf A z := by
    simpa only [hLevel] using hX
  have hLeafFinal :
      IsLeaf (finiteCanonicalCausalMarkerGraph DA)
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i z hzn)).val :=
    (finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
      DA i z hLeafSource.1 hzn).1.mpr hLeafSource
  simpa only [hRank] using hLeafFinal

/-- Every selected off-branch pair has two genuine final-graph
leaf roles at its actual finite numerical endpoints. -/
theorem finiteCanonicalCausalMarkerGraph_masked_pair_leaves
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (y z : Nat)
    (hm : finiteCanonicalRankedOffBranchMask DA y z) :
    IsLeaf (finiteCanonicalCausalMarkerGraph DA) y ∧
    IsLeaf (finiteCanonicalCausalMarkerGraph DA) z := by
  obtain ⟨Y,Z,hY,hZ,hOff⟩ := hm
  have hLeafY :=
    finiteCanonicalCausalMarkerGraph_leaf_at_rank
      DA Y hOff.leafY
  have hLeafZ :=
    finiteCanonicalCausalMarkerGraph_leaf_at_rank
      DA Z hOff.leafZ
  constructor
  · simpa only [hY] using hLeafY
  · simpa only [hZ] using hLeafZ

end DiaryLeafPriority
end ThreeUniformDiaries
