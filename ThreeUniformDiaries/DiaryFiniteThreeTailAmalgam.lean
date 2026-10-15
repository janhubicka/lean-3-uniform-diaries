import ThreeUniformDiaries.AuxTypes

/-!
# Finite ordered amalgamation of two three-tail source pictures

Take two genuine finite pointed source pictures with the same
protected prefix n and three exterior positions (split, first
leaf, second leaf). To make one calibration triple we identify
their split vertices and identify the SECOND leaf of the first
picture with the FIRST leaf of the second picture.

The resulting ordered source has four exterior positions:
   n        split,
   n+1      first picture's first leaf,
   n+2      shared central leaf,
   n+3      second picture's second leaf.

The first source maps identically into the first n+3 vertices.
The second source maps its first n+1 vertices identically and
shifts its two leaf positions by one.

We state the exact induced-edge compatibility on their overlap
and prove that it yields a FREE amalgam containing both finite
sources as induced ordered hypergraphs. No false overlap
identifications and no order reversal are used.

IMPORTANT: this is only the edge-level finite amalgamation.
The finite AUXILIARY type-respecting embedding codes require
an additional early-distinction argument across the inserted
vertex. The global orientation witness is not claimed here.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Insert one new position immediately after n in a
finite ordered three-tail picture. The split n stays fixed,
while the first/second exterior leaves shift by one. -/
def threeTailShift (n t : Nat) : Nat :=
  if t ≤ n then t else t + 1

theorem threeTailShift_strictMono (n : Nat) :
    StrictMono (threeTailShift n) := by
  intro a b hab
  unfold threeTailShift
  by_cases ha : a ≤ n
  · by_cases hb : b ≤ n
    · simp [ha, hb]
      omega
    · simp [ha, hb]
      omega
  · have hb : ¬ b ≤ n := by omega
    simp [ha, hb]
    omega

theorem threeTailShift_prefix (n t : Nat) (ht : t ≤ n) :
    threeTailShift n t = t := by
  simp [threeTailShift, ht]

theorem threeTailShift_firstLeaf (n : Nat) :
    threeTailShift n (n+1) = n+2 := by
  simp [threeTailShift]

theorem threeTailShift_secondLeaf (n : Nat) :
    threeTailShift n (n+2) = n+3 := by
  simp [threeTailShift]

/-- Exactly the overlap condition needed to identify the
protected prefix, the split n, and the shared central leaf.
All increasing triples of the second picture BEFORE its
last exterior leaf must agree with their corresponding
triples in the first picture. -/
def ThreeTailOverlapCompatible
    (A B : Ordered3Graph Nat) (n : Nat) : Prop :=
  ∀ x y z, x < y → y < z → z < n + 2 →
    (A.edge (threeTailShift n x)
       (threeTailShift n y) (threeTailShift n z) ↔
     B.edge x y z)

/-- The literal ordered free amalgam. Until its last new
vertex n+3 the relation is exactly A. At the last vertex
we copy the B-relation through the strictly increasing
three-tail shift map and declare all unsupported cross
triples false. Beyond this finite carrier the relation
is false, providing a harmless countable continuation. -/
def threeTailFreeAmalgam
    (A B : Ordered3Graph Nat) (n : Nat) : Ordered3Graph Nat where
  edge x y z :=
    if z < n+3 then A.edge x y z
    else
      ∃ x' y' z' : Nat,
        x' < y' ∧ y' < z' ∧ z' < n+3 ∧
        threeTailShift n x' = x ∧
        threeTailShift n y' = y ∧
        threeTailShift n z' = z ∧
        B.edge x' y' z'

/-- The first three-tail source occurs as the literal initial
ordered induced subhypergraph of the free amalgam. -/
theorem threeTailFreeAmalgam_left
    (A B : Ordered3Graph Nat) (n x y z : Nat)
    (hz : z < n+3) :
    (threeTailFreeAmalgam A B n).edge x y z ↔
      A.edge x y z := by
  simp [threeTailFreeAmalgam, hz]

/-- Every increasing triple of the second three-tail source
is preserved AND reflected by the shifted embedding into
the four-tail amalgam. The proof treats triples on the
shared overlap separately from triples containing the
new final leaf. -/
theorem threeTailFreeAmalgam_right
    (A B : Ordered3Graph Nat) (n : Nat)
    (hOverlap : ThreeTailOverlapCompatible A B n)
    (x y z : Nat) (hxy : x < y) (hyz : y < z)
    (hz : z < n+3) :
    (threeTailFreeAmalgam A B n).edge
      (threeTailShift n x)
      (threeTailShift n y)
      (threeTailShift n z) ↔
    B.edge x y z := by
  have hmono : StrictMono (threeTailShift n) :=
    threeTailShift_strictMono n
  by_cases hsmall : z < n+2
  · have hmapBound : threeTailShift n z < n+3 := by
      unfold threeTailShift
      split_ifs <;> omega
    change
      (if threeTailShift n z < n+3 then
         A.edge (threeTailShift n x) (threeTailShift n y)
           (threeTailShift n z)
       else ∃ x' y' z' : Nat,
         x' < y' ∧ y' < z' ∧ z' < n+3 ∧
         threeTailShift n x' = threeTailShift n x ∧
         threeTailShift n y' = threeTailShift n y ∧
         threeTailShift n z' = threeTailShift n z ∧
         B.edge x' y' z') ↔ B.edge x y z
    rw [if_pos hmapBound]
    exact hOverlap x y z hxy hyz hsmall
  · have hlast : z = n+2 := by omega
    have hmapLast : threeTailShift n z = n+3 := by
      subst z
      exact threeTailShift_secondLeaf n
    have hnot : ¬ threeTailShift n z < n+3 := by omega
    change
      (if threeTailShift n z < n+3 then
         A.edge (threeTailShift n x) (threeTailShift n y)
           (threeTailShift n z)
       else ∃ x' y' z' : Nat,
         x' < y' ∧ y' < z' ∧ z' < n+3 ∧
         threeTailShift n x' = threeTailShift n x ∧
         threeTailShift n y' = threeTailShift n y ∧
         threeTailShift n z' = threeTailShift n z ∧
         B.edge x' y' z') ↔ B.edge x y z
    rw [if_neg hnot]
    constructor
    · rintro ⟨x', y', z', hxy', hyz', hz', hx', hy', hz'', hEdge⟩
      have hxEq : x' = x := hmono.injective hx'
      have hyEq : y' = y := hmono.injective hy'
      have hzEq : z' = z := hmono.injective hz''
      simpa only [hxEq, hyEq, hzEq] using hEdge
    · intro hEdge
      exact ⟨x, y, z, hxy, hyz, hz, rfl, rfl, rfl, hEdge⟩

end Ordered3Graph
end ThreeUniformDiaries
