import ThreeUniformDiaries.DiaryFiniteCanonicalCausalCrossSourcePairTypes

/-!
# A shared causal source 2-split is the full meet of opposing branch pairs

At a shared source two-split s, two ordered leaf pairs from distinct
canonical flips can have the SAME complete source pair-type code
strictly before s while choosing OPPOSITE E3 bits at s. The
nonpositive causal predecessor transport theorem proves that
their ACTUAL full target pair types agree before the numbered
rank m of s. The induced original-branch edge table preserves
the opposite auxiliary bits at m. Thus the full pair-type meet
of these CROSSBRANCH pairs is exactly m.

This identifies a true target S2 witness spanning DIFFERENT
canonical branches, without assuming the causal graph itself
satisfies global S2. The proof is finite and precedes any
dummy-tail, one-pass or support compression; those transports
are separate obligations for flip-feedback injectivity.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- When original source full pair-code prefixes agree at one
shared 2-split but the current E3 bits disagree, the full
pair-type meet in the finite causal marker graph is EXACTLY
the common ranked split, even though the compared pairs
come from DIFFERENT canonical source flips. -/
theorem finiteCanonicalCausalMarkerGraph_crossTwoMeet_exact_at_sharedSplit
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i j : FiniteCanonicalFlipIndex A n)
    (s u v w z : Nat)
    (hs : IsTwoSplit A s)
    (hsn : s < n)
    (hShared :
      (finiteCanonicalSignRootedFamily DA).node i s =
      (finiteCanonicalSignRootedFamily DA).node j s)
    (huv : u < v) (hwz : w < z)
    (hvn : v < n) (hzn : z < n)
    (hsu : s < u) (hsw : s < w)
    (hu : IsLeaf ((finiteCanonicalSignRootedFamily DA).graph i) u)
    (hv : IsLeaf ((finiteCanonicalSignRootedFamily DA).graph i) v)
    (hw : IsLeaf ((finiteCanonicalSignRootedFamily DA).graph j) w)
    (hz : IsLeaf ((finiteCanonicalSignRootedFamily DA).graph j) z)
    (hCode :
      twoCode ((finiteCanonicalSignRootedFamily DA).graph i) s u v =
      twoCode ((finiteCanonicalSignRootedFamily DA).graph j) s w z)
    (hDifferent :
      ¬ (((finiteCanonicalSignRootedFamily DA).graph i).edge s u v ↔
         ((finiteCanonicalSignRootedFamily DA).graph j).edge s w z)) :
    (finiteCanonicalCausalMarkerGraph DA).twoMeetLevel
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i v hvn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA j w (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA j z hzn)).val =
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let G := finiteCanonicalCausalMarkerGraph DA
  let m := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i s hsn)).val
  let aa := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i u (by omega))).val
  let bb := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i v hvn)).val
  let cc := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA j w (by omega))).val
  let dd := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA j z hzn)).val
  have hPrefix : G.SameTwoTypeBelow m aa bb cc dd :=
    finiteCanonicalCausalMarkerGraph_sharedTwoSplit_parent_of_source_codes
      DA i j s u v w z hs hsn hShared
      huv hwz hvn hzn hsu hsw hu hv hw hz hCode
  have hmA : m < aa :=
    finiteCanonicalNodeAt_index_lt DA i s u hsu (by omega)
  have hSharedRank :
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val =
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA j s hsn)).val := by
    have hEq : finiteCanonicalNodeAt DA i s hsn =
        finiteCanonicalNodeAt DA j s hsn :=
      Subtype.ext hShared
    exact congrArg
      (fun T : FiniteCanonicalSignRootedVertex DA =>
        (finiteCanonicalNodeIndex DA T).val) hEq
  have hmC : m < cc := by
    have hj := finiteCanonicalNodeAt_index_lt DA j s w hsw (by omega)
    change (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA j s hsn)).val < cc at hj
    dsimp only [m]
    rw [hSharedRank]
    exact hj
  have hLower : m ≤ G.twoMeetLevel aa bb cc dd := by
    apply Nat.le_findGreatest (by omega)
    exact hPrefix
  have hI : G.edge m aa bb ↔ (F.graph i).edge s u v :=
    finiteCanonicalCausalMarkerGraph_branch_edge_iff
      DA i s u v hsu huv hvn
  have hJ : G.edge m cc dd ↔ (F.graph j).edge s w z := by
    dsimp only [m]
    rw [hSharedRank]
    exact finiteCanonicalCausalMarkerGraph_branch_edge_iff
      DA j s w z hsw hwz hzn
  have hTargetDifferent :
      ¬ (G.edge m aa bb ↔ G.edge m cc dd) := by
    intro hSame
    exact hDifferent (hI.symm.trans (hSame.trans hJ))
  have hUpper : G.twoMeetLevel aa bb cc dd ≤ m := by
    by_contra h
    have hGreater : m < G.twoMeetLevel aa bb cc dd := by omega
    have hAgree := G.twoMeetLevel_agree aa bb cc dd
    exact hTargetDifferent (hAgree.2.2 hGreater)
  change G.twoMeetLevel aa bb cc dd = m
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
