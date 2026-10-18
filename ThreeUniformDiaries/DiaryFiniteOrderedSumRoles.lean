import ThreeUniformDiaries.DiaryFiniteOrderedSumCarrier

/-!
# Marker-defined roles of the two finite diary blocks

Inside the raw ordered-sum carrier, both original vertex blocks
are induced, but this alone is worth spelling out at the level
of the manuscript's marker-defined leaf/one-split/two-split roles.

For each original left nonmarker vertex u<n, both role marker
edges (0,1,u) and (0,2,u) are reflected exactly. For each
original right nonmarker v<m, the analogous edges at its
translated image reflect those of K. Thus each of the three
roles is transported AND reflected on either block, for
arbitrary cross-copy Boolean orientation assignments.

This is one component of the finite ordered-sum V/E proof;
the positive split coherence and global Devlin V3 remain
independent mathematical obligations.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- The two literal role marker bits of any left nonmarker
vertex agree with the source, for every cross orientation. -/
theorem finiteTwoBlockCarrier_left_role_bits
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool) (u : Nat) (hun : u < n) :
    (((finiteTwoBlockCarrier H K n m bits).edge 0 1 u ↔ H.edge 0 1 u) ∧
     ((finiteTwoBlockCarrier H K n m bits).edge 0 2 u ↔ H.edge 0 2 u)) := by
  exact ⟨finiteTwoBlockCarrier_left_edge_iff FH FK bits 0 1 u hun,
    finiteTwoBlockCarrier_left_edge_iff FH FK bits 0 2 u hun⟩

/-- The two literal role marker bits of any translated right
nonmarker vertex agree with K, including negative reflections. -/
theorem finiteTwoBlockCarrier_right_role_bits
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool) (v : Nat) (hvm : v < m) :
    (((finiteTwoBlockCarrier H K n m bits).edge
        0 1 (rightBlockImage n v) ↔ K.edge 0 1 v) ∧
     ((finiteTwoBlockCarrier H K n m bits).edge
        0 2 (rightBlockImage n v) ↔ K.edge 0 2 v)) := by
  constructor
  · simpa [rightBlockImage] using
      (finiteTwoBlockCarrier_right_edge_iff
        FH FK bits 0 1 v hvm)
  · simpa [rightBlockImage] using
      (finiteTwoBlockCarrier_right_edge_iff
        FH FK bits 0 2 v hvm)

/-- Leaf role is preserved and reflected on the left block. -/
theorem finiteTwoBlockCarrier_left_leaf_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool) (u : Nat) (hun : u < n) :
    IsLeaf (finiteTwoBlockCarrier H K n m bits) u ↔ IsLeaf H u := by
  have hrole := finiteTwoBlockCarrier_left_role_bits
    FH FK bits u hun
  simp only [IsLeaf, hrole.1, hrole.2]

/-- 1-split role is preserved and reflected on the left block. -/
theorem finiteTwoBlockCarrier_left_oneSplit_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool) (u : Nat) (hun : u < n) :
    IsOneSplit (finiteTwoBlockCarrier H K n m bits) u ↔ IsOneSplit H u := by
  have hrole := finiteTwoBlockCarrier_left_role_bits
    FH FK bits u hun
  simp only [IsOneSplit, hrole.1, hrole.2]

/-- 2-split role is preserved and reflected on the left block. -/
theorem finiteTwoBlockCarrier_left_twoSplit_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool) (u : Nat) (hun : u < n) :
    IsTwoSplit (finiteTwoBlockCarrier H K n m bits) u ↔ IsTwoSplit H u := by
  have hrole := finiteTwoBlockCarrier_left_role_bits
    FH FK bits u hun
  simp only [IsTwoSplit, hrole.1, hrole.2]

/-- Leaf role is transported and reflected on the right block. -/
theorem finiteTwoBlockCarrier_right_leaf_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool) (v : Nat)
    (hv3 : 3 ≤ v) (hvm : v < m) :
    IsLeaf (finiteTwoBlockCarrier H K n m bits)
      (rightBlockImage n v) ↔ IsLeaf K v := by
  have hmarker := finiteTwoBlockCarrier_right_role_bits
    FH FK bits v hvm
  have hge : 3 ≤ rightBlockImage n v := by
    have hBound := rightBlockImage_nonmarker_ge n v
      FH.length_ge_three hv3
    have hn3 := FH.length_ge_three
    omega
  constructor
  · intro h
    exact ⟨hv3, fun he => h.2.1 (hmarker.1.mpr he),
      fun he => h.2.2 (hmarker.2.mpr he)⟩
  · intro h
    exact ⟨hge, fun he => h.2.1 (hmarker.1.mp he),
      fun he => h.2.2 (hmarker.2.mp he)⟩

/-- 1-split role is transported and reflected on the right block. -/
theorem finiteTwoBlockCarrier_right_oneSplit_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool) (v : Nat)
    (hv3 : 3 ≤ v) (hvm : v < m) :
    IsOneSplit (finiteTwoBlockCarrier H K n m bits)
      (rightBlockImage n v) ↔ IsOneSplit K v := by
  have hmarker := finiteTwoBlockCarrier_right_role_bits
    FH FK bits v hvm
  have hge : 3 ≤ rightBlockImage n v := by
    have hBound := rightBlockImage_nonmarker_ge n v
      FH.length_ge_three hv3
    have hn3 := FH.length_ge_three
    omega
  constructor
  · intro h
    exact ⟨hv3, hmarker.1.mp h.2.1,
      fun he => h.2.2 (hmarker.2.mpr he)⟩
  · intro h
    exact ⟨hge, hmarker.1.mpr h.2.1,
      fun he => h.2.2 (hmarker.2.mp he)⟩

/-- 2-split role is transported and reflected on the right block. -/
theorem finiteTwoBlockCarrier_right_twoSplit_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool) (v : Nat)
    (hv3 : 3 ≤ v) (hvm : v < m) :
    IsTwoSplit (finiteTwoBlockCarrier H K n m bits)
      (rightBlockImage n v) ↔ IsTwoSplit K v := by
  have hmarker := finiteTwoBlockCarrier_right_role_bits
    FH FK bits v hvm
  have hge : 3 ≤ rightBlockImage n v := by
    have hBound := rightBlockImage_nonmarker_ge n v
      FH.length_ge_three hv3
    have hn3 := FH.length_ge_three
    omega
  constructor
  · intro h
    exact ⟨hv3, fun he => h.2.1 (hmarker.1.mpr he),
      hmarker.2.mp h.2.2⟩
  · intro h
    exact ⟨hge, fun he => h.2.1 (hmarker.1.mp he),
      hmarker.2.mpr h.2.2⟩

end DiaryLeafPriority
end ThreeUniformDiaries
