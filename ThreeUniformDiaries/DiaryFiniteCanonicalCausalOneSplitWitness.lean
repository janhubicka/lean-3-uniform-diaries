import ThreeUniformDiaries.DiaryFiniteCanonicalCausalRoleCensus
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalOriginalOneMeet

/-!
# Global bounded one-split witnesses in the completed causal graph

For an arbitrary actual target 1-split of the concrete finite
causal sign-rooted graph, the finite node census supplies an
original source-flip branch vertex at precisely that numerical
rank. Exact marker-role reflection identifies the corresponding
source 1-split.

The source branch's genuine finite diary already provides two
leaf witnesses with original singleton meet equal to that split.
Both leaf images are bounded, are genuine final leaves, and the
verified original-meet preservation theorem (#906) shows that
their final singleton meet is EXACTLY the target split rank.

This proves the complete bounded V1 witness field required for
a finite pre-diary, independent of globally quantified V1
coherence, V2 and the absorption theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every actual 1-split of the completed finite causal graph
has two bounded target leaves strictly after it whose exact
singleton meet is that 1-split, with no extra geometric choices. -/
theorem finiteCanonicalCausalMarkerGraph_global_oneSplit_witness
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (s : Nat)
    (hs : IsOneSplit (finiteCanonicalCausalMarkerGraph DA) s)
    (hsBound : s < Fintype.card (FiniteCanonicalSignRootedVertex DA)) :
    ∃ a b : Nat,
      a < Fintype.card (FiniteCanonicalSignRootedVertex DA) ∧
      b < Fintype.card (FiniteCanonicalSignRootedVertex DA) ∧
      IsLeaf (finiteCanonicalCausalMarkerGraph DA) a ∧
      IsLeaf (finiteCanonicalCausalMarkerGraph DA) b ∧
      s < a ∧ s < b ∧
      (finiteCanonicalCausalMarkerGraph DA).oneMeetLevel a b = s := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let G := finiteCanonicalCausalMarkerGraph DA
  obtain ⟨i,t,htn,hRankS⟩ :=
    finiteCanonicalNodeIndex_census DA s hsBound
  have ht3 : 3 ≤ t := by
    by_contra h
    have hsmall : t < 3 := by omega
    have hMarker :=
      finiteCanonicalMarker_index_of_lt_three DA i t hsmall htn
    have hS3 : 3 ≤ s := hs.1
    omega
  have hSplitSource : IsOneSplit A t := by
    have hRoles :=
      finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
        DA i t ht3 htn
    have hAtIndex : IsOneSplit G
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i t htn)).val := by
      simpa only [hRankS] using hs
    exact hRoles.2.1.mp hAtIndex
  have hSplitFlip : IsOneSplit (F.graph i) t :=
    ((F.flip i).role_iff t ht3 htn).2.1.mp hSplitSource
  obtain ⟨u,v,hun,hvn,huF,hvF,htu,htv,hMeet⟩ :=
    (F.flip i).target_diary.prediary.one_split_witness
      t hSplitFlip htn
  have huA : IsLeaf A u :=
    ((F.flip i).role_iff u huF.1 hun).1.mpr huF
  have hvA : IsLeaf A v :=
    ((F.flip i).role_iff v hvF.1 hvn).1.mpr hvF
  let a := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i u hun)).val
  let b := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i v hvn)).val
  have hBoundA :
      a < Fintype.card (FiniteCanonicalSignRootedVertex DA) :=
    (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i u hun)).isLt
  have hBoundB :
      b < Fintype.card (FiniteCanonicalSignRootedVertex DA) :=
    (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i v hvn)).isLt
  have hLeafA : IsLeaf G a :=
    (finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
      DA i u huA.1 hun).1.mpr huA
  have hLeafB : IsLeaf G b :=
    (finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
      DA i v hvA.1 hvn).1.mpr hvA
  have hSA : s < a := by
    have h := finiteCanonicalNodeAt_index_lt DA i t u htu hun
    simpa only [hRankS] using h
  have hSB : s < b := by
    have h := finiteCanonicalNodeAt_index_lt DA i t v htv hvn
    simpa only [hRankS] using h
  have hExact : G.oneMeetLevel a b = s := by
    have h := finiteCanonicalCausalMarkerGraph_original_proper_oneMeet_exact
      DA i t u v hSplitSource htn htu htv hun hvn
        huA hvA hMeet
    simpa only [hRankS] using h
  exact ⟨a,b,hBoundA,hBoundB,hLeafA,hLeafB,hSA,hSB,hExact⟩

end DiaryLeafPriority
end ThreeUniformDiaries
