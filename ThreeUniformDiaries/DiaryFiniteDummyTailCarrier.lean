import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface
import ThreeUniformDiaries.DiaryFiniteOrderedSumCarrier

/-!
# An explicit infinite dummy-leaf tail after a finite pre-diary

Let H have all edges supported below n, with its true finite diary
roles on [3,n). The countable tail carrier fixes the entire old
finite initial segment, including all old edges AND nonedges.

For each old leaf u<n and each new tail vertex z>=n, add exactly
one of the two Devlin marker edges (1,u,z) and (2,u,z), with
a Boolean parameter depending on u but INDEPENDENT of z.
For every pair of tail vertices n<=u<z, add (1,u,z) and do
not add (2,u,z). No normal/split-positive edges touch the tail.

The resulting graph is an actual ordered ternary relation on Nat;
all tail vertices have the marker-defined leaf role. This file
proves only the carrier's edge classification, role invariants and
induced finite prefix. A globally coherent choice of the old-leaf
orientation bits, tail V3, and countable V/E pre-diary axioms
remain separate obligations.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Extend a finitely supported source ternary graph by infinitely
many dummy leaves, retaining ALL original internal nonedges.
There are only old-to-tail and tail-to-tail Devlin marker edges. -/
noncomputable def finiteDummyTailCarrier
    (H : Ordered3Graph Nat) (n : Nat)
    (bits : Nat → Bool) : Ordered3Graph Nat where
  edge x y z :=
    (H.edge x y z ∧ z < n) ∨
    (∃ u : Nat, 3 ≤ u ∧ u < n ∧ IsLeaf H u ∧ n ≤ z ∧
      y = u ∧
      ((x = 1 ∧ bits u = true) ∨
       (x = 2 ∧ bits u = false))) ∨
    (x = 1 ∧ n ≤ y ∧ y < z)

variable {H : Ordered3Graph Nat} {n : Nat}

/-- Every new edge is a strictly increasing ordered triple. -/
theorem finiteDummyTailCarrier_edge_ordered
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (x y z : Nat)
    (he : (finiteDummyTailCarrier H n bits).edge x y z) :
    x < y ∧ y < z := by
  have hn3 := FH.length_ge_three
  rcases he with hOld | hCross | hTail
  · have h := FH.edge_support x y z hOld.1
    exact ⟨h.1,h.2.1⟩
  · obtain ⟨u,hu3,hun,_hLeaf,hzn,hy,hBit⟩ := hCross
    rcases hBit with hOne | hTwo
    · omega
    · omega
  · omega

/-- Exact induced preservation of the source finite edge AND
nonedge relation on its old bounded initial segment. -/
theorem finiteDummyTailCarrier_finite_edge_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (x y z : Nat) (hzn : z < n) :
    (finiteDummyTailCarrier H n bits).edge x y z ↔ H.edge x y z := by
  constructor
  · intro he
    rcases he with hOld | hCross | hTail
    · exact hOld.1
    · obtain ⟨u,_hu3,_hun,_hleaf,hge,_hy,_hbit⟩ := hCross
      omega
    · omega
  · intro he
    exact Or.inl ⟨he,hzn⟩

/-- Every old source edge is retained, since finite support
puts its last vertex below the original boundary. -/
theorem finiteDummyTailCarrier_old_edge_iff_all
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (x y z : Nat) (hzn : z < n) :
    (finiteDummyTailCarrier H n bits).edge x y z ↔ H.edge x y z :=
  finiteDummyTailCarrier_finite_edge_iff FH bits x y z hzn

/-- Old vertex role-marker bits survive exactly in the tail
carrier, for all source vertices in the finite frame. -/
theorem finiteDummyTailCarrier_old_role_bits
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (z : Nat) (hzn : z < n) :
    (((finiteDummyTailCarrier H n bits).edge 0 1 z ↔ H.edge 0 1 z) ∧
     ((finiteDummyTailCarrier H n bits).edge 0 2 z ↔ H.edge 0 2 z)) := by
  exact ⟨finiteDummyTailCarrier_finite_edge_iff
    FH bits 0 1 z hzn,
    finiteDummyTailCarrier_finite_edge_iff
    FH bits 0 2 z hzn⟩

/-- Every added tail vertex is genuinely a marker-defined leaf,
not a split, independently of the old orientation parameter. -/
theorem finiteDummyTailCarrier_tail_isLeaf
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (z : Nat) (hzn : n ≤ z) :
    IsLeaf (finiteDummyTailCarrier H n bits) z := by
  have hz3 : 3 ≤ z := by
    have hn3 := FH.length_ge_three
    omega
  refine ⟨hz3, ?_, ?_⟩
  · intro he
    rcases he with hOld | hCross | hTail
    · omega
    · obtain ⟨u,_hu3,_hun,_hLeaf,_hge,_hy,hBit⟩ := hCross
      rcases hBit with hOne | hTwo
      · omega
      · omega
    · omega
  · intro he
    rcases he with hOld | hCross | hTail
    · omega
    · obtain ⟨u,_hu3,_hun,_hLeaf,_hge,_hy,hBit⟩ := hCross
      rcases hBit with hOne | hTwo
      · omega
      · omega
    · omega

/-- For each old leaf and ANY tail leaf, marker one records
exactly the designated Boolean orientation. -/
theorem finiteDummyTailCarrier_cross_one_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (u z : Nat) (hu3 : 3 ≤ u) (hun : u < n)
    (huLeaf : IsLeaf H u) (hzn : n ≤ z) :
    (finiteDummyTailCarrier H n bits).edge 1 u z ↔
      bits u = true := by
  constructor
  · intro he
    rcases he with hOld | hCross | hTail
    · omega
    · obtain ⟨v,_hv3,_hvn,_hvLeaf,_hzn,hy,hBit⟩ := hCross
      have hv : v = u := hy.symm
      subst v
      rcases hBit with hOne | hTwo
      · exact hOne.2
      · omega
    · omega
  · intro hb
    exact Or.inr (Or.inl
      ⟨u,hu3,hun,huLeaf,hzn,rfl,Or.inl ⟨rfl,hb⟩⟩)

/-- Cross marker two is exactly the complementary chosen bit. -/
theorem finiteDummyTailCarrier_cross_two_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (u z : Nat) (hu3 : 3 ≤ u) (hun : u < n)
    (huLeaf : IsLeaf H u) (hzn : n ≤ z) :
    (finiteDummyTailCarrier H n bits).edge 2 u z ↔
      bits u = false := by
  constructor
  · intro he
    rcases he with hOld | hCross | hTail
    · omega
    · obtain ⟨v,_hv3,_hvn,_hvLeaf,_hzn,hy,hBit⟩ := hCross
      have hv : v = u := hy.symm
      subst v
      rcases hBit with hOne | hTwo
      · omega
      · exact hTwo.2
    · omega
  · intro hb
    exact Or.inr (Or.inl
      ⟨u,hu3,hun,huLeaf,hzn,rfl,Or.inr ⟨rfl,hb⟩⟩)

/-- Two distinct tail leaves always carry Devlin marker one. -/
theorem finiteDummyTailCarrier_tail_pair_marker_one
    (bits : Nat → Bool)
    (u z : Nat) (hun : n ≤ u) (huz : u < z) :
    (finiteDummyTailCarrier H n bits).edge 1 u z :=
  Or.inr (Or.inr ⟨rfl,hun,huz⟩)

/-- Devlin marker two is absent on every ordered pair of tail
vertices, independently of all finite cross orientation bits. -/
theorem finiteDummyTailCarrier_tail_pair_marker_two_false
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (u z : Nat) (hun : n ≤ u) (huz : u < z) :
    ¬ (finiteDummyTailCarrier H n bits).edge 2 u z := by
  intro he
  rcases he with hOld | hCross | hTail
  · omega
  · obtain ⟨v,_hv3,hvn,_hLeaf,_hzn,hy,hBit⟩ := hCross
    omega
  · omega

end DiaryLeafPriority
end ThreeUniformDiaries
