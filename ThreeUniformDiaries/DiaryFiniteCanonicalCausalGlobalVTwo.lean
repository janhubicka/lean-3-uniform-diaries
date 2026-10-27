import ThreeUniformDiaries.DiaryFiniteCanonicalCausalGlobalVOne
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalVTwoCoherence

/-!
# Globally quantified V2 coherence on the completed sign-rooted carrier

All non-Devlin edges of the completed causal graph are inherited
from genuine canonical source-flip branches. Given two arbitrary
positive V2 incidences (s,a,b) and (s,c,d) at the same true
target 2-split, use these source-edge witnesses and injectivity of
the finite ranking to identify their shared original source split.

The completed vertex-role census reflects all four leaf roles and
the shared 2-split back to their source. The previously verified
causal V2-positive-parent theorem (#913) then proves the EXACT
full predecessor pair-type agreement at the numbered target cut.

This is precisely the globally quantified V2 coherence field of
the finite pre-diary interface. It is not a split witness, an
S-meet theorem or finite flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Complete global V2 positive-parent coherence, for any two
positive ordered pairs of target leaves at any actual target
2-split in the completed causal sign-rooted graph. -/
theorem finiteCanonicalCausalMarkerGraph_global_twoSplit_coherent
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (s a b c d : Nat)
    (hs : IsTwoSplit (finiteCanonicalCausalMarkerGraph DA) s)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf (finiteCanonicalCausalMarkerGraph DA) a)
    (hb : IsLeaf (finiteCanonicalCausalMarkerGraph DA) b)
    (hc : IsLeaf (finiteCanonicalCausalMarkerGraph DA) c)
    (hd : IsLeaf (finiteCanonicalCausalMarkerGraph DA) d)
    (hsab : (finiteCanonicalCausalMarkerGraph DA).edge s a b)
    (hscd : (finiteCanonicalCausalMarkerGraph DA).edge s c d) :
    (finiteCanonicalCausalMarkerGraph DA).SameTwoTypeBelow
      s a b c d := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let G := finiteCanonicalCausalMarkerGraph DA
  have hs1 : s ≠ 1 := by have hs3 := hs.1; omega
  have hs2 : s ≠ 2 := by have hs3 := hs.1; omega
  obtain ⟨i,p,u,v,hpu,huv,hS,hA,hB,hPosI⟩ :=
    finiteCanonicalCausalMarkerGraph_nonDevlin_source_witness
      DA s a b hs1 hs2 hsab
  obtain ⟨j,q,w,z,hqw,hwz,hS',hC,hD,hPosJ⟩ :=
    finiteCanonicalCausalMarkerGraph_nonDevlin_source_witness
      DA s c d hs1 hs2 hscd
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
      finiteCanonicalMarker_index_of_lt_three DA i p.val
        hpSmall p.isLt
    have hs3 : 3 ≤ s := hs.1
    omega
  have hps : IsTwoSplit A p.val := by
    have hRoles :=
      finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
        DA i p.val hp3 p.isLt
    have hTarget : IsTwoSplit G
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i p.val p.isLt)).val := by
      simpa only [hS] using hs
    exact hRoles.2.2.mp hTarget
  have hu3 : 3 ≤ u.val := by omega
  have hv3 : 3 ≤ v.val := by omega
  have hw3 : 3 ≤ w.val := by omega
  have hz3 : 3 ≤ z.val := by omega
  have huA : IsLeaf A u.val := by
    have hRoles := finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
      DA i u.val hu3 u.isLt
    have hTarget : IsLeaf G
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i u.val u.isLt)).val := by
      simpa only [hA] using ha
    exact hRoles.1.mp hTarget
  have hvA : IsLeaf A v.val := by
    have hRoles := finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
      DA i v.val hv3 v.isLt
    have hTarget : IsLeaf G
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i v.val v.isLt)).val := by
      simpa only [hB] using hb
    exact hRoles.1.mp hTarget
  have hwA : IsLeaf A w.val := by
    have hRoles := finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
      DA j w.val hw3 w.isLt
    have hTarget : IsLeaf G
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA j w.val w.isLt)).val := by
      simpa only [hC] using hc
    exact hRoles.1.mp hTarget
  have hzA : IsLeaf A z.val := by
    have hRoles := finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
      DA j z.val hz3 z.isLt
    have hTarget : IsLeaf G
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA j z.val z.isLt)).val := by
      simpa only [hD] using hd
    exact hRoles.1.mp hTarget
  have huF : IsLeaf (F.graph i) u.val :=
    ((F.flip i).role_iff u.val huA.1 u.isLt).1.mp huA
  have hvF : IsLeaf (F.graph i) v.val :=
    ((F.flip i).role_iff v.val hvA.1 v.isLt).1.mp hvA
  have hwF : IsLeaf (F.graph j) w.val :=
    ((F.flip j).role_iff w.val hwA.1 w.isLt).1.mp hwA
  have hzF : IsLeaf (F.graph j) z.val :=
    ((F.flip j).role_iff z.val hzA.1 z.isLt).1.mp hzA
  have hpw : p.val < w.val := by omega
  have hPosJ' : (F.graph j).edge p.val w.val z.val := by
    simpa only [← hpq] using hPosJ
  have hV2 :=
    finiteCanonicalCausalMarkerGraph_sharedTwoSplit_positive_parent
      DA i j p.val u.val v.val w.val z.val
      hps p.isLt hShared huv hwz v.isLt z.isLt
      hpu hpw huF hvF hwF hzF hPosI hPosJ'
  simpa only [hS,hA,hB,hC,hD] using hV2

end DiaryLeafPriority
end ThreeUniformDiaries
