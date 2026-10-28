import ThreeUniformDiaries.DiaryFiniteCanonicalCausalVTwoCoherence

/-!
# Crossbranch source-code transport through the causal sign-rooted graph

The global positive-class V2 lemma previously covered TWO
SOURCE-POSITIVE pairs at a shared 2-split. The precise first
disagreement argument for feedback instead compares two copies
of the SAME source ordered leaf pair whose E3 bits at the
current split may be OPPOSITE.

For such pairs positivity cannot be assumed on both sides.
What is sufficient is exact source twoCode equality strictly
below the shared split. This file transports that equality
across ALL offbranch raw nodes, the actual finite ranked
carrier, and the completed crossbranch Devlin-marker mask.
The proof invokes no global S1/S2 of the finite causal graph.
Neither crossbranch exact meets after one-pass completion nor
arbitrary target-flip absorption is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Source full pair-type CODE equality through the SHARED source
cut transports to the actual ranked raw graph's predecessor
pair type, including all off-path vertices and tied source levels.
Unlike V2-positive coherence, neither pair must be positive at
the split. -/
theorem finiteCanonicalRankedRaw_sharedTwoSplit_parent_of_source_codes
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i j : FiniteCanonicalFlipIndex A n)
    (s u v w z : Nat)
    (hsn : s < n)
    (hShared :
      (finiteCanonicalSignRootedFamily DA).node i s =
      (finiteCanonicalSignRootedFamily DA).node j s)
    (huv : u < v) (hwz : w < z)
    (hvn : v < n) (hzn : z < n)
    (hsu : s < u) (hsw : s < w)
    (hCode :
      twoCode ((finiteCanonicalSignRootedFamily DA).graph i) s u v =
      twoCode ((finiteCanonicalSignRootedFamily DA).graph j) s w z) :
    (finiteCanonicalRankedRawGraph DA).SameTwoTypeBelow
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i v hvn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA j w (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA j z hzn)).val := by
  let F := finiteCanonicalSignRootedFamily DA
  have hRaw :=
    F.rawCrossTwoTypeBelow_of_source_codes
      i j s u v w z hShared hsu.le hsw.le
      huv hwz hvn hzn hCode
  exact ⟨
    finiteCanonicalRankedRaw_crossOneType_at_shared_cut
      DA i j s u w hsn hShared hsu.le hsw.le
      (by omega) (by omega) hRaw.1,
    finiteCanonicalRankedRaw_crossOneType_at_shared_cut
      DA i j s v z hsn hShared (by omega) (by omega)
      hvn hzn hRaw.2.1,
    finiteCanonicalRankedRaw_crossAux_at_shared_cut
      DA i j s u v w z hsn hShared hsu.le hsw.le
      huv hwz hvn hzn hRaw.2.2⟩

/-- Complete full predecessor pair-type equality in the ACTUAL
finite causal sign-rooted graph from arbitrary matching source
pair codes below a SHARED two-split. Neither source ordered
leaf pair is required to be positive at this split.
This is stronger than V2 coherence at positive pairs. -/
theorem finiteCanonicalCausalMarkerGraph_sharedTwoSplit_parent_of_source_codes
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
      twoCode ((finiteCanonicalSignRootedFamily DA).graph j) s w z) :
    (finiteCanonicalCausalMarkerGraph DA).SameTwoTypeBelow
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i v hvn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA j w (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA j z hzn)).val := by
  let F := finiteCanonicalSignRootedFamily DA
  let R := finiteCanonicalRankedRawGraph DA
  let M := finiteCanonicalRankedOffBranchMask DA
  let G := finiteCanonicalCausalMarkerGraph DA
  let m := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i s hsn)).val
  let a := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i u (by omega))).val
  let b := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i v hvn)).val
  let c := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA j w (by omega))).val
  let d := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA j z hzn)).val
  have huA : IsLeaf A u :=
    ((F.flip i).role_iff u hu.1 (by omega)).1.mpr hu
  have hvA : IsLeaf A v :=
    ((F.flip i).role_iff v hv.1 hvn).1.mpr hv
  have hwA : IsLeaf A w :=
    ((F.flip j).role_iff w hw.1 (by omega)).1.mpr hw
  have hzA : IsLeaf A z :=
    ((F.flip j).role_iff z hz.1 hzn).1.mpr hz
  have hRaw : R.SameTwoTypeBelow m a b c d :=
    finiteCanonicalRankedRaw_sharedTwoSplit_parent_of_source_codes
      DA i j s u v w z hsn hShared
      huv hwz hvn hzn hsu hsw hCode
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
  have hma : m ≤ a :=
    (finiteCanonicalNodeAt_index_lt DA i s u hsu (by omega)).le
  have hmb : m ≤ b :=
    (finiteCanonicalNodeAt_index_lt DA i s v (by omega) hvn).le
  have hmc : m ≤ c := by
    have hj := finiteCanonicalNodeAt_index_lt DA j s w hsw (by omega)
    change (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA j s hsn)).val < c at hj
    dsimp only [m]
    rw [hSharedRank]
    exact hj.le
  have hmd : m ≤ d := by
    have hj := finiteCanonicalNodeAt_index_lt DA j s z (by omega) hzn
    change (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA j s hsn)).val < d at hj
    dsimp only [m]
    rw [hSharedRank]
    exact hj.le
  have hMaskAC : SameEarlierMarkerMask M m a c :=
    finiteCanonicalRankedOffBranchMask_sharedSplit_below
      DA i j s u w (Or.inr hs) hsn hShared
      hsu hsw (by omega) (by omega) huA hwA
  have hMaskBD : SameEarlierMarkerMask M m b d :=
    finiteCanonicalRankedOffBranchMask_sharedSplit_below
      DA i j s v z (Or.inr hs) hsn hShared
      (by omega) (by omega) hvn hzn hvA hzA
  have hLater : ∀ x y, M x y → x < y :=
    finiteCanonicalRankedOffBranchMask_later DA
  have hOneAC : G.SameOneTypeBelow m a c :=
    causalMarker_preserves_parent_oneType R G M m a c
      hma hmc hRaw.1 hMaskAC
      (by
        intro x y hxy hys
        exact causalMarkerLimit_formula R M hLater x y a)
      (by
        intro x y hxy hys
        exact causalMarkerLimit_formula R M hLater x y c)
  have hOneBD : G.SameOneTypeBelow m b d :=
    causalMarker_preserves_parent_oneType R G M m b d
      hmb hmd hRaw.2.1 hMaskBD
      (by
        intro x y hxy hys
        exact causalMarkerLimit_formula R M hLater x y b)
      (by
        intro x y hxy hys
        exact causalMarkerLimit_formula R M hLater x y d)
  have hAux : G.SameAuxTypeBelow m a b c d := by
    intro x hx
    have hI := finiteCanonicalCausalMarkerGraph_aux_edge_iff_raw_on_branch
      DA i u v huv hvn x
    have hJ := finiteCanonicalCausalMarkerGraph_aux_edge_iff_raw_on_branch
      DA j w z hwz hzn x
    exact hI.trans ((hRaw.2.2 hx).trans hJ.symm)
  exact ⟨hOneAC,hOneBD,hAux⟩

end DiaryLeafPriority
end ThreeUniformDiaries
