import ThreeUniformDiaries.DiaryFiniteCanonicalCausalOriginalTwoMeet
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalRoleCensus

/-!
# Global bounded two-split witnesses in the concrete causal graph

The source finite diary already contains four bounded leaves
witnessing the exact full two-meet at every genuine source 2-split.
The canonical finite rank enumerates every target vertex, and
exact marker-role reflection identifies any target 2-split with
some source 2-split on one of the canonical flip branches.

The verified original exact full two-meet theorem transports the
two source witness pairs to the actual causally completed graph
without changing their meet. Source increasing-order and roles
are also preserved at the rank indices.

This proves the full bounded two-split witness field in the
manuscript's finite pre-diary interface, completing its remaining
V/E witness obligation without using S1/S2 for the output graph.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- EVERY actual target 2-split below the finite sign-rooted
carrier bound has four bounded target leaves forming two ordered
pairs whose exact full pair-type meet is this target split. -/
theorem finiteCanonicalCausalMarkerGraph_global_twoSplit_witness
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (s : Nat)
    (hs : IsTwoSplit (finiteCanonicalCausalMarkerGraph DA) s)
    (hsBound : s < Fintype.card (FiniteCanonicalSignRootedVertex DA)) :
    ∃ a b c d : Nat,
      a < b ∧ c < d ∧
      a < Fintype.card (FiniteCanonicalSignRootedVertex DA) ∧
      b < Fintype.card (FiniteCanonicalSignRootedVertex DA) ∧
      c < Fintype.card (FiniteCanonicalSignRootedVertex DA) ∧
      d < Fintype.card (FiniteCanonicalSignRootedVertex DA) ∧
      IsLeaf (finiteCanonicalCausalMarkerGraph DA) a ∧
      IsLeaf (finiteCanonicalCausalMarkerGraph DA) b ∧
      IsLeaf (finiteCanonicalCausalMarkerGraph DA) c ∧
      IsLeaf (finiteCanonicalCausalMarkerGraph DA) d ∧
      s < a ∧ s < c ∧
      (finiteCanonicalCausalMarkerGraph DA).twoMeetLevel a b c d = s := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let G := finiteCanonicalCausalMarkerGraph DA
  obtain ⟨i,t,htn,hRankS⟩ :=
    finiteCanonicalNodeIndex_census DA s hsBound
  have ht3 : 3 ≤ t := by
    by_contra h
    have htSmall : t < 3 := by omega
    have hRank :=
      finiteCanonicalMarker_index_of_lt_three DA i t htSmall htn
    have hs3 : 3 ≤ s := hs.1
    omega
  have hSplitA : IsTwoSplit A t := by
    have hRoles :=
      finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
        DA i t ht3 htn
    have hAtRank : IsTwoSplit G
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i t htn)).val := by
      simpa only [hRankS] using hs
    exact hRoles.2.2.mp hAtRank
  have hSplitF : IsTwoSplit (F.graph i) t :=
    ((F.flip i).role_iff t ht3 htn).2.2.mp hSplitA
  obtain ⟨a,b,c,d,hab,hcd,han,hbn,hcn,hdn,
    haF,hbF,hcF,hdF,hta,htc,hMeet⟩ :=
    (F.flip i).target_diary.prediary.two_split_witness
      t hSplitF htn
  have haA : IsLeaf A a :=
    ((F.flip i).role_iff a haF.1 han).1.mpr haF
  have hbA : IsLeaf A b :=
    ((F.flip i).role_iff b hbF.1 hbn).1.mpr hbF
  have hcA : IsLeaf A c :=
    ((F.flip i).role_iff c hcF.1 hcn).1.mpr hcF
  have hdA : IsLeaf A d :=
    ((F.flip i).role_iff d hdF.1 hdn).1.mpr hdF
  let ra := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i a han)).val
  let rb := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i b hbn)).val
  let rc := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i c hcn)).val
  let rd := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i d hdn)).val
  have hBoundA :
      ra < Fintype.card (FiniteCanonicalSignRootedVertex DA) :=
    (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i a han)).isLt
  have hBoundB :
      rb < Fintype.card (FiniteCanonicalSignRootedVertex DA) :=
    (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i b hbn)).isLt
  have hBoundC :
      rc < Fintype.card (FiniteCanonicalSignRootedVertex DA) :=
    (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i c hcn)).isLt
  have hBoundD :
      rd < Fintype.card (FiniteCanonicalSignRootedVertex DA) :=
    (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i d hdn)).isLt
  have hAB : ra < rb :=
    finiteCanonicalNodeAt_index_lt DA i a b hab hbn
  have hCD : rc < rd :=
    finiteCanonicalNodeAt_index_lt DA i c d hcd hdn
  have hLeafA : IsLeaf G ra :=
    (finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
      DA i a haA.1 han).1.mpr haA
  have hLeafB : IsLeaf G rb :=
    (finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
      DA i b hbA.1 hbn).1.mpr hbA
  have hLeafC : IsLeaf G rc :=
    (finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
      DA i c hcA.1 hcn).1.mpr hcA
  have hLeafD : IsLeaf G rd :=
    (finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
      DA i d hdA.1 hdn).1.mpr hdA
  have hSA : s < ra := by
    have h := finiteCanonicalNodeAt_index_lt DA i t a hta han
    simpa only [hRankS] using h
  have hSC : s < rc := by
    have h := finiteCanonicalNodeAt_index_lt DA i t c htc hcn
    simpa only [hRankS] using h
  have hExact : G.twoMeetLevel ra rb rc rd = s := by
    have h := finiteCanonicalCausalMarkerGraph_original_twoMeet_exact_at_twoSplit
      DA i t a b c d hSplitA htn hta htc
      hab hcd hbn hdn haA hbA hcA hdA hMeet
    simpa only [hRankS] using h
  exact ⟨ra,rb,rc,rd,hAB,hCD,hBoundA,hBoundB,hBoundC,hBoundD,
    hLeafA,hLeafB,hLeafC,hLeafD,hSA,hSC,hExact⟩

end DiaryLeafPriority
end ThreeUniformDiaries
