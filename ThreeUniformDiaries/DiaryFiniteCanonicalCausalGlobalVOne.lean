import ThreeUniformDiaries.DiaryFiniteCanonicalCausalSourceEdgeCensus
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalVOneCoherence

/-!
# Globally quantified V1 coherence on the canonical causal carrier

An arbitrary positive V1 incidence (0,s,a) in the completed causal
graph cannot be a newly inserted Devlin marker edge. Its actual
source-branch witness is provided by the non-Devlin edge census.

For two such incidences (0,s,a), (0,s,b), injectivity of the exact
finite rank index makes their two source split nodes coincide. The
complete role census reflects the target 1-split and leaf roles back
to their source-flip branches. Thus they satisfy the hypotheses of
the previously verified cross-branch positive V1 theorem (#911).

This discharges the globally quantified one-split-coherence field
of the finite pre-diary interface, without assuming any V1 premise
on the completed causal graph. The bounded split witnesses and V2
coherence fields remain independent.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Full V1 positive-parent coherence for EVERY target one-split
and EVERY two leaves positively incident with that split in the
final causal sign-rooted graph. No branch hypotheses remain. -/
theorem finiteCanonicalCausalMarkerGraph_global_oneSplit_coherent
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (s a b : Nat)
    (hs : IsOneSplit (finiteCanonicalCausalMarkerGraph DA) s)
    (ha : IsLeaf (finiteCanonicalCausalMarkerGraph DA) a)
    (hb : IsLeaf (finiteCanonicalCausalMarkerGraph DA) b)
    (hsa : (finiteCanonicalCausalMarkerGraph DA).edge 0 s a)
    (hsb : (finiteCanonicalCausalMarkerGraph DA).edge 0 s b) :
    (finiteCanonicalCausalMarkerGraph DA).SameOneTypeBelow s a b := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let G := finiteCanonicalCausalMarkerGraph DA
  obtain ⟨i,p,u,hp0,hpu,hS,hA,hPosI⟩ :=
    finiteCanonicalCausalMarkerGraph_zero_edge_source_witness
      DA s a hsa
  obtain ⟨j,q,v,hq0,hqv,hS',hB,hPosJ⟩ :=
    finiteCanonicalCausalMarkerGraph_zero_edge_source_witness
      DA s b hsb
  have hSameNode :
      finiteCanonicalNodeAt DA i p.val p.isLt =
        finiteCanonicalNodeAt DA j q.val q.isLt := by
    apply finiteCanonicalNodeIndex_injective DA
    exact Fin.ext (hS.trans hS'.symm)
  have hpq : p.val = q.val := by
    have h := congrArg
      (fun T : FiniteCanonicalSignRootedVertex DA => T.val.1)
      hSameNode
    simpa only [finiteCanonicalNodeAt_level] using h
  have hShared :
      F.node i p.val = F.node j p.val := by
    have h := congrArg Subtype.val hSameNode
    change F.node i p.val = F.node j q.val at h
    simpa only [← hpq] using h
  have hp3 : 3 ≤ p.val := by
    by_contra h
    have hpSmall : p.val < 3 := by omega
    have hMarkerRank :=
      finiteCanonicalMarker_index_of_lt_three
        DA i p.val hpSmall p.isLt
    have hs3 : 3 ≤ s := hs.1
    omega
  have hps : IsOneSplit A p.val := by
    have hRoles :=
      finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
        DA i p.val hp3 p.isLt
    have hTarget : IsOneSplit G
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i p.val p.isLt)).val := by
      simpa only [hS] using hs
    exact hRoles.2.1.mp hTarget
  have hu3 : 3 ≤ u.val := by omega
  have hv3 : 3 ≤ v.val := by omega
  have huA : IsLeaf A u.val := by
    have hRoles :=
      finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
        DA i u.val hu3 u.isLt
    have hTarget : IsLeaf G
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i u.val u.isLt)).val := by
      simpa only [hA] using ha
    exact hRoles.1.mp hTarget
  have hvA : IsLeaf A v.val := by
    have hRoles :=
      finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
        DA j v.val hv3 v.isLt
    have hTarget : IsLeaf G
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA j v.val v.isLt)).val := by
      simpa only [hB] using hb
    exact hRoles.1.mp hTarget
  have huF : IsLeaf (F.graph i) u.val :=
    ((F.flip i).role_iff u.val huA.1 u.isLt).1.mp huA
  have hvF : IsLeaf (F.graph j) v.val :=
    ((F.flip j).role_iff v.val hvA.1 v.isLt).1.mp hvA
  have hpv : p.val < v.val := by omega
  have hPosJ' : (F.graph j).edge 0 p.val v.val := by
    simpa only [← hpq] using hPosJ
  have hV1 :=
    finiteCanonicalCausalMarkerGraph_sharedOneSplit_positive_parent
      DA i j p.val u.val v.val hps p.isLt
      hShared hpu hpv u.isLt v.isLt
      huF hvF hPosI hPosJ'
  simpa only [hS,hA,hB] using hV1

end DiaryLeafPriority
end ThreeUniformDiaries
