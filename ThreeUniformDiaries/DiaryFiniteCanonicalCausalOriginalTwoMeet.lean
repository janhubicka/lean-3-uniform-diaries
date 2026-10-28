import ThreeUniformDiaries.DiaryFiniteCanonicalCausalOriginalTwoType
import ThreeUniformDiaries.DiaryFiniteLeafMeetTwoSplitDisagreement

/-!
# Exact old pair meets at genuine source two-splits in the causal graph

An S2 witness in a genuine finite source-flip diary consists of
two ordered leaf pairs whose full pair-type meet is a source
2-split s. The previous rank-cut theorem established equality
of all their complete predecessor types THROUGH the actual
numerical rank of s in the final causal sign-rooted graph.

The verified E1--E5 first-difference lemma says that a full
pair meet located at a genuine two-split must be detected by
opposite auxiliary incidences at that split: the source E3
bits E(s,a,b) and E(s,c,d) are unequal. Each ordered pair
stays inside the SAME original source-flip branch, whose
induced edge table survives the causal extension, so these
two final bits are also unequal at the exact numerical rank.

Hence the final full pair meet is exactly the rank of s.
No V2-positive orientation assumption or completed S2 axiom
is used. This is the exact mixed-meet fact needed to retain
all bounded source 2-split witnesses.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- If an original pair of ordered source leaf pairs has
full meet exactly at a genuine 2-split s, then its full
meet in the ACTUAL completed causal graph is exactly the
numerical rank of that source split. Both singleton and
auxiliary predecessor tests are accounted for, including
all inserted off-path nodes and tied original levels. -/
theorem finiteCanonicalCausalMarkerGraph_original_twoMeet_exact_at_twoSplit
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (s a b c d : Nat)
    (hs : IsTwoSplit A s)
    (hsn : s < n) (hsa : s < a) (hsc : s < c)
    (hab : a < b) (hcd : c < d)
    (hbn : b < n) (hdn : d < n)
    (ha : IsLeaf A a) (hb : IsLeaf A b)
    (hc : IsLeaf A c) (hd : IsLeaf A d)
    (hSourceMeet :
      ((finiteCanonicalSignRootedFamily DA).graph i).twoMeetLevel
        a b c d = s) :
    (finiteCanonicalCausalMarkerGraph DA).twoMeetLevel
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i a (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i b hbn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i c (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i d hdn)).val =
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let G := finiteCanonicalCausalMarkerGraph DA
  let m := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i s hsn)).val
  let aa := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i a (by omega))).val
  let bb := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i b hbn)).val
  let cc := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i c (by omega))).val
  let dd := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i d hdn)).val
  have hSourceType : (F.graph i).SameTwoTypeBelow s a b c d := by
    have h := (F.graph i).twoMeetLevel_agree a b c d
    rw [hSourceMeet] at h
    exact h
  have hFinalType : G.SameTwoTypeBelow m aa bb cc dd :=
    finiteCanonicalCausalMarkerGraph_original_twoType_at_twoSplit
      DA i s a b c d hs hsn hsa hsc hab hcd hbn hdn
      ha hb hc hd hSourceType
  have hMA : m < aa :=
    finiteCanonicalNodeAt_index_lt DA i s a hsa (by omega)
  have hMC : m < cc :=
    finiteCanonicalNodeAt_index_lt DA i s c hsc (by omega)
  have hLower : m ≤ G.twoMeetLevel aa bb cc dd := by
    apply Nat.le_findGreatest (by omega)
    exact hFinalType
  have hSplitFlip : IsTwoSplit (F.graph i) s :=
    ((F.flip i).role_iff s hs.1 hsn).2.2.mp hs
  have hSourceDiff :
      ¬ ((F.graph i).edge s a b ↔ (F.graph i).edge s c d) :=
    E_twoSplit_pair_aux_distinguishes
      (F.flip i).target_diary.prediary.permitted_edge
      s a b c d hSplitFlip hsa hsc hSourceMeet
  have hEA : G.edge m aa bb ↔ (F.graph i).edge s a b :=
    finiteCanonicalCausalMarkerGraph_branch_edge_iff
      DA i s a b hsa hab hbn
  have hEC : G.edge m cc dd ↔ (F.graph i).edge s c d :=
    finiteCanonicalCausalMarkerGraph_branch_edge_iff
      DA i s c d hsc hcd hdn
  have hFinalDiff :
      ¬ (G.edge m aa bb ↔ G.edge m cc dd) := by
    intro h
    exact hSourceDiff (hEA.symm.trans (h.trans hEC))
  have hUpper : G.twoMeetLevel aa bb cc dd ≤ m := by
    by_contra h
    have hGt : m < G.twoMeetLevel aa bb cc dd := by omega
    exact hFinalDiff ((G.twoMeetLevel_agree aa bb cc dd).2.2 (a := m) hGt)
  change G.twoMeetLevel aa bb cc dd = m
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
