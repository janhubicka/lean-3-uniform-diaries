import ThreeUniformDiaries.DiaryFiniteLeafMeetOrderReindex

/-!
# The three distinguished markers survive finite support reindexing

When a finite support S contains markers 0,1,2, the increasing
Finset.orderEmbOfFin enumeration sends its first three indices
to EXACTLY these markers. This is proved from surjectivity and
the elementary inequality i <= S[i] for a strictly increasing
enumeration of natural numbers.

It follows that any induced finite graph on S reflects the
original two marker-role incidences (0,1,v) and (0,2,v).
Consequently all genuine nonmarker vertices of the restriction
retain their literal leaf/one-split/two-split roles.

These are the marker and role prerequisites for extracting a
finite diary from a leaf-meet support. No V1/V2 witnesses,
Devlin V3 or meet preservation is inferred merely from roles.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A strictly increasing enumeration of natural numbers
cannot map its index i to a value smaller than i. -/
theorem finiteSupportIndex_ge_index
    (S : Finset Nat) (i : Nat) (hi : i < S.card) :
    i ≤ finiteSupportIndex S i := by
  induction i with
  | zero =>
      omega
  | succ i ih =>
      have hiPrev : i < S.card := by omega
      have hPrev := ih hiPrev
      have hStrict :=
        finiteSupportIndex_strictMono S i (i + 1)
          (by omega) hi
      omega

/-- If 0,1,2 belong to the support, then the first three
indices exist and enumerate exactly 0,1,2. -/
theorem finiteSupportIndex_initial_markers
    (S : Finset Nat)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S) :
    3 ≤ S.card ∧
      finiteSupportIndex S 0 = 0 ∧
      finiteSupportIndex S 1 = 1 ∧
      finiteSupportIndex S 2 = 2 := by
  obtain ⟨i0,hi0,he0⟩ :=
    finiteSupportIndex_surjective_on S 0 h0
  have hIndex0 := finiteSupportIndex_ge_index S i0 hi0
  have hi0Eq : i0 = 0 := by omega
  have hAt0 : finiteSupportIndex S 0 = 0 := by
    simpa only [hi0Eq] using he0
  obtain ⟨i1,hi1,he1⟩ :=
    finiteSupportIndex_surjective_on S 1 h1
  have hIndex1 := finiteSupportIndex_ge_index S i1 hi1
  have hi1Ne0 : i1 ≠ 0 := by
    intro h
    rw [h,hAt0] at he1
    omega
  have hi1Eq : i1 = 1 := by omega
  have hAt1 : finiteSupportIndex S 1 = 1 := by
    simpa only [hi1Eq] using he1
  obtain ⟨i2,hi2,he2⟩ :=
    finiteSupportIndex_surjective_on S 2 h2
  have hIndex2 := finiteSupportIndex_ge_index S i2 hi2
  have hi2Ne0 : i2 ≠ 0 := by
    intro h
    rw [h,hAt0] at he2
    omega
  have hi2Ne1 : i2 ≠ 1 := by
    intro h
    rw [h,hAt1] at he2
    omega
  have hi2Eq : i2 = 2 := by omega
  have hAt2 : finiteSupportIndex S 2 = 2 := by
    simpa only [hi2Eq] using he2
  have hCard : 3 ≤ S.card := by
    have h2lt : 2 < S.card := by
      simpa only [hi2Eq] using hi2
    omega
  exact ⟨hCard,hAt0,hAt1,hAt2⟩

/-- The actual generator support always contains the three
markers, and its increasing reindexing fixes them pointwise. -/
theorem finiteLeafMeetSupport_reindex_markers
    (G : Ordered3Graph Nat) (L : Finset Nat) :
    let S := finiteLeafMeetSupport G L
    3 ≤ S.card ∧
      finiteSupportIndex S 0 = 0 ∧
      finiteSupportIndex S 1 = 1 ∧
      finiteSupportIndex S 2 = 2 := by
  dsimp
  exact finiteSupportIndex_initial_markers
    (finiteLeafMeetSupport G L)
    (mem_finiteLeafMeetSupport_marker G L 0 (by omega))
    (mem_finiteLeafMeetSupport_marker G L 1 (by omega))
    (mem_finiteLeafMeetSupport_marker G L 2 (by omega))

variable {G : Ordered3Graph Nat} {S : Finset Nat}

/-- Marker (0,1,i) is reflected exactly when the finite
ordered support enumeration fixes the initial three markers. -/
theorem finiteSupportGraph_marker_one_iff
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S)
    (i : Nat) (hi3 : 3 ≤ i) (hin : i < S.card) :
    (finiteSupportGraph G S).edge 0 1 i ↔
      G.edge 0 1 (finiteSupportIndex S i) := by
  obtain ⟨_,hZero,hOne,_⟩ :=
    finiteSupportIndex_initial_markers S h0 h1 h2
  have hEdge := finiteSupportGraph_edge_iff
    G S 0 1 i (by omega) (by omega) hin
  simpa only [hZero,hOne] using hEdge

/-- Marker (0,2,i) is reflected exactly. -/
theorem finiteSupportGraph_marker_two_iff
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S)
    (i : Nat) (hi3 : 3 ≤ i) (hin : i < S.card) :
    (finiteSupportGraph G S).edge 0 2 i ↔
      G.edge 0 2 (finiteSupportIndex S i) := by
  obtain ⟨_,hZero,_,hTwo⟩ :=
    finiteSupportIndex_initial_markers S h0 h1 h2
  have hEdge := finiteSupportGraph_edge_iff
    G S 0 2 i (by omega) (by omega) hin
  simpa only [hZero,hTwo] using hEdge

/-- Actual marker-defined LEAF roles survive finite reindexing. -/
theorem finiteSupportGraph_leaf_iff
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S)
    (i : Nat) (hi3 : 3 ≤ i) (hin : i < S.card) :
    IsLeaf (finiteSupportGraph G S) i ↔
      IsLeaf G (finiteSupportIndex S i) := by
  have hIndex := finiteSupportIndex_ge_index S i hin
  have h3 : 3 ≤ finiteSupportIndex S i := by omega
  have hOne := finiteSupportGraph_marker_one_iff
    (G := G) h0 h1 h2 i hi3 hin
  have hTwo := finiteSupportGraph_marker_two_iff
    (G := G) h0 h1 h2 i hi3 hin
  constructor
  · intro h
    exact ⟨h3,
      fun he => h.2.1 (hOne.mpr he),
      fun he => h.2.2 (hTwo.mpr he)⟩
  · intro h
    exact ⟨hi3,
      fun he => h.2.1 (hOne.mp he),
      fun he => h.2.2 (hTwo.mp he)⟩

/-- Actual marker-defined 1-SPLIT roles survive reindexing. -/
theorem finiteSupportGraph_oneSplit_iff
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S)
    (i : Nat) (hi3 : 3 ≤ i) (hin : i < S.card) :
    IsOneSplit (finiteSupportGraph G S) i ↔
      IsOneSplit G (finiteSupportIndex S i) := by
  have hIndex := finiteSupportIndex_ge_index S i hin
  have h3 : 3 ≤ finiteSupportIndex S i := by omega
  have hOne := finiteSupportGraph_marker_one_iff
    (G := G) h0 h1 h2 i hi3 hin
  have hTwo := finiteSupportGraph_marker_two_iff
    (G := G) h0 h1 h2 i hi3 hin
  constructor
  · intro h
    exact ⟨h3,hOne.mp h.2.1,fun he => h.2.2 (hTwo.mpr he)⟩
  · intro h
    exact ⟨hi3,hOne.mpr h.2.1,fun he => h.2.2 (hTwo.mp he)⟩

/-- Actual marker-defined 2-SPLIT roles survive reindexing. -/
theorem finiteSupportGraph_twoSplit_iff
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S)
    (i : Nat) (hi3 : 3 ≤ i) (hin : i < S.card) :
    IsTwoSplit (finiteSupportGraph G S) i ↔
      IsTwoSplit G (finiteSupportIndex S i) := by
  have hIndex := finiteSupportIndex_ge_index S i hin
  have h3 : 3 ≤ finiteSupportIndex S i := by omega
  have hOne := finiteSupportGraph_marker_one_iff
    (G := G) h0 h1 h2 i hi3 hin
  have hTwo := finiteSupportGraph_marker_two_iff
    (G := G) h0 h1 h2 i hi3 hin
  constructor
  · intro h
    exact ⟨h3,
      fun he => h.2.1 (hOne.mpr he),
      hTwo.mp h.2.2⟩
  · intro h
    exact ⟨hi3,
      fun he => h.2.1 (hOne.mp he),
      hTwo.mpr h.2.2⟩

end DiaryLeafPriority
end ThreeUniformDiaries
