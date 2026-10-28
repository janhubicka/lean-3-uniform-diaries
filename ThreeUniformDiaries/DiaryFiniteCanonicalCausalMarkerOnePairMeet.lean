import ThreeUniformDiaries.DiaryFiniteCanonicalCausalOriginalV3
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalPermittedEdges

/-!
# Exact marker-one full pair meets in the causal sign-rooted graph

The manuscript's full S2 has a marker-one alternative: two ordered
pairs of original source leaves can first differ in their Devlin
marker-one bit, with full twoMeetLevel equal to 1.

For ANY ordered ternary graph satisfying E1--E5, a genuine leaf
cannot be the middle vertex of an edge beginning at marker zero.
Together with the marker-defined leaf roles, all pairs of leaf
pairs have equal full types below cut 1. Moreover, if their full
meet is exactly 1, their marker-one auxiliary E(1,a,b) bits MUST
differ: if these bits also agreed, all tests through cut 2 would
agree, contradicting maximality of the meet.

The actual causal completion preserves every source branch
inducedly AND fixes the numerical index of marker 1. Hence the
first-difference bit at 1 survives. The final leaf roles and E
condition force full type equality through cut 1, so the final
full twoMeetLevel is exactly 1.

This covers the marker-one S2 case for every chosen source branch.
It does not assert all cross-branch S2 comparisons or flip
absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- A true leaf cannot be the middle vertex of an edge beginning
at the source role marker zero, by the actual five E forms. -/
theorem permitted_no_zero_edge_through_leaf
    (hE : ∀ x y z, H.edge x y z → PermittedDiaryEdge H x y z)
    (u v : Nat) (hu : IsLeaf H u) :
    ¬ H.edge 0 u v := by
  intro he
  have hu3 : 3 ≤ u := hu.1
  rcases hE 0 u v he with hE1 | hE2 | hE3 | hE4 | hE5
  · rcases hE1 with ⟨_, huMark, _⟩
    rcases huMark with hu1 | hu2 <;> omega
  · exact hu.2.1 hE2.2.1.2.1
  · have hBad : 3 ≤ (0 : Nat) := hE3.1.1
    omega
  · rcases hE4.1 with h1 | h2 <;> omega
  · have hBad : 3 ≤ (0 : Nat) := hE5.1.1
    omega

/-- Every two ordered leaf pairs have the same full predecessor
pair type through cut 1, without assuming S2 or any diary axioms. -/
theorem permitted_leaf_pairs_sameTwoTypeBelow_one
    (hE : ∀ x y z, H.edge x y z → PermittedDiaryEdge H x y z)
    (a b c d : Nat)
    (ha : IsLeaf H a) (hc : IsLeaf H c) :
    H.SameTwoTypeBelow 1 a b c d := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy hy
    omega
  · intro x y hxy hy
    omega
  · intro x hx
    have hx0 : x = 0 := by omega
    subst x
    exact iff_of_false
      (permitted_no_zero_edge_through_leaf hE a b ha)
      (permitted_no_zero_edge_through_leaf hE c d hc)

/-- A full source pair meet at marker 1 is necessarily witnessed
by disagreement in the literal marker-one auxiliary edge bits.
The singleton marker-profile tests through cut 2 are equal for
all leaves and the marker-zero pair tests are forbidden by E1--E5. -/
theorem permitted_marker_one_pair_meet_distinguishes
    (hE : ∀ x y z, H.edge x y z → PermittedDiaryEdge H x y z)
    (a b c d : Nat)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hMeet : H.twoMeetLevel a b c d = 1) :
    ¬ (H.edge 1 a b ↔ H.edge 1 c d) := by
  classical
  have hNotNext : ¬ H.SameTwoTypeBelow 2 a b c d := by
    intro hNext
    have hCap : 2 ≤ min a c := by
      have ha3 := ha.1
      have hc3 := hc.1
      omega
    have hGreater : 2 ≤ H.twoMeetLevel a b c d :=
      Nat.le_findGreatest hCap hNext
    omega
  intro hBit
  apply hNotNext
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy hy
    have hy1 : y = 1 := by omega
    have hx0 : x = 0 := by omega
    subst y
    subst x
    exact iff_of_false ha.2.1 hc.2.1
  · intro x y hxy hy
    have hy1 : y = 1 := by omega
    have hx0 : x = 0 := by omega
    subst y
    subst x
    exact iff_of_false hb.2.1 hd.2.1
  · intro x hx
    rcases Nat.eq_zero_or_pos x with hx0 | hxPos
    · subst x
      exact iff_of_false
        (permitted_no_zero_edge_through_leaf hE a b ha)
        (permitted_no_zero_edge_through_leaf hE c d hc)
    · have hx1 : x = 1 := by omega
      simpa only [hx1] using hBit

/-- Exact source full pair meet at marker one remains exactly one
in the FINAL canonical causal sign-rooted graph. All four leaves
belong to the same original canonical flip branch; no source
S2 axiom is assumed in the completed graph. -/
theorem finiteCanonicalCausalMarkerGraph_original_markerOne_twoMeet_exact
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (hbn : b < n) (hdn : d < n)
    (ha : IsLeaf A a) (hb : IsLeaf A b)
    (hc : IsLeaf A c) (hd : IsLeaf A d)
    (hSourceMeet :
      ((finiteCanonicalSignRootedFamily DA).graph i).twoMeetLevel
        a b c d = 1) :
    (finiteCanonicalCausalMarkerGraph DA).twoMeetLevel
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i a (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i b hbn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i c (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i d hdn)).val = 1 := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let G := finiteCanonicalCausalMarkerGraph DA
  let aa := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i a (by omega))).val
  let bb := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i b hbn)).val
  let cc := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i c (by omega))).val
  let dd := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i d hdn)).val
  have haFinal : IsLeaf G aa :=
    (finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
      DA i a ha.1 (by omega)).1.mpr ha
  have hcFinal : IsLeaf G cc :=
    (finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
      DA i c hc.1 (by omega)).1.mpr hc
  have hAtOne : G.SameTwoTypeBelow 1 aa bb cc dd :=
    permitted_leaf_pairs_sameTwoTypeBelow_one
      (finiteCanonicalCausalMarkerGraph_permitted_edge DA)
      aa bb cc dd haFinal hcFinal
  have hLower : 1 ≤ G.twoMeetLevel aa bb cc dd := by
    apply Nat.le_findGreatest (by
      have ha3 := haFinal.1
      have hc3 := hcFinal.1
      omega)
    exact hAtOne
  have hLeafFA : IsLeaf (F.graph i) a :=
    ((F.flip i).role_iff a ha.1 (by omega)).1.mp ha
  have hLeafFB : IsLeaf (F.graph i) b :=
    ((F.flip i).role_iff b hb.1 hbn).1.mp hb
  have hLeafFC : IsLeaf (F.graph i) c :=
    ((F.flip i).role_iff c hc.1 (by omega)).1.mp hc
  have hLeafFD : IsLeaf (F.graph i) d :=
    ((F.flip i).role_iff d hd.1 hdn).1.mp hd
  have hDiffSource :
      ¬ ((F.graph i).edge 1 a b ↔ (F.graph i).edge 1 c d) :=
    permitted_marker_one_pair_meet_distinguishes
      (F.flip i).target_diary.prediary.permitted_edge
      a b c d hLeafFA hLeafFB hLeafFC hLeafFD hSourceMeet
  have hOneRank : (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i 1 (by
        have hn := DA.prediary.frame.length_ge_three
        omega))).val = 1 :=
    finiteCanonicalMarker_one_rank DA i
  have haAfterOne : 1 < a := by
    have ha3 := ha.1
    omega
  have hcAfterOne : 1 < c := by
    have hc3 := hc.1
    omega
  have hEdgeAB : G.edge 1 aa bb ↔ (F.graph i).edge 1 a b := by
    have h := finiteCanonicalCausalMarkerGraph_branch_edge_iff
      DA i 1 a b haAfterOne hab hbn
    simpa only [hOneRank] using h
  have hEdgeCD : G.edge 1 cc dd ↔ (F.graph i).edge 1 c d := by
    have h := finiteCanonicalCausalMarkerGraph_branch_edge_iff
      DA i 1 c d hcAfterOne hcd hdn
    simpa only [hOneRank] using h
  have hDiffFinal : ¬ (G.edge 1 aa bb ↔ G.edge 1 cc dd) := by
    intro h
    exact hDiffSource (hEdgeAB.symm.trans (h.trans hEdgeCD))
  have hUpper : G.twoMeetLevel aa bb cc dd ≤ 1 := by
    by_contra h
    have hGT : 1 < G.twoMeetLevel aa bb cc dd := by omega
    have hFull : G.SameTwoTypeBelow
        (G.twoMeetLevel aa bb cc dd) aa bb cc dd :=
      G.twoMeetLevel_agree aa bb cc dd
    have hAux : G.SameAuxTypeBelow
        (G.twoMeetLevel aa bb cc dd) aa bb cc dd := hFull.2.2
    exact hDiffFinal (hAux (a := 1) hGT)
  change G.twoMeetLevel aa bb cc dd = 1
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
