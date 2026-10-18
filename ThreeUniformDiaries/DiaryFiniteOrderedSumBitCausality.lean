import ThreeUniformDiaries.DiaryFiniteOrderedSumFuturePrefix
import ThreeUniformDiaries.DiaryLexPrefixEdgeInvariance

/-!
# Causality of finite ordered-sum marker choices

The raw finite two-block carrier takes one Boolean orientation bit
for each left leaf. Suppose two such assignments agree at all
positions strictly below a fixed left vertex u.

Then the literal LexEarlier comparison of u with ANY genuine right
leaf is unchanged. This statement includes changes to the bit at
u itself and to every later bit: neither can influence the test
which chooses the bit at u.

The proof reduces to columns with middle coordinate below u:
the terminal u is in the induced left copy and is independent of
all cross bits, while the later right leaf's prefix column is
exactly the uniform cross marker encoded by the earlier left
leaf. The generic lex-prefix invariance theorem completes the
argument. No V1/V2/V3 or diary meet axioms are assumed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- The actual future-leaf edge columns before the left vertex u
depend only on the orientation values at earlier left leaves.
Changing the current or later orientation bits cannot affect
the corresponding edge tests. -/
theorem finiteTwoBlockCarrier_right_column_prefix_congr
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hshape : ∀ a b c : Nat, K.edge a b c →
      PermittedDiaryEdge K a b c)
    (orientation orientation' : Nat → Bool)
    (u v : Nat) (hu : u < n)
    (hv3 : 3 ≤ v) (hvm : v < m) (hvLeaf : IsLeaf K v)
    (hBefore : ∀ t : Nat, t < u → orientation t = orientation' t) :
    ∀ a b : Nat, a < b → b < u →
      ((finiteTwoBlockCarrier H K n m orientation).edge
          a b (rightBlockImage n v) ↔
       (finiteTwoBlockCarrier H K n m orientation').edge
          a b (rightBlockImage n v)) := by
  intro a b hab hb
  have hbn : b < n := by omega
  calc
    (finiteTwoBlockCarrier H K n m orientation).edge
        a b (rightBlockImage n v) ↔
      (3 ≤ b ∧ IsLeaf H b ∧
        ((a = 1 ∧ orientation b = true) ∨
         (a = 2 ∧ orientation b = false))) :=
      finiteTwoBlockCarrier_right_leaf_column_iff
        FH FK hshape orientation a b v hab hbn hv3 hvm hvLeaf
    _ ↔ (3 ≤ b ∧ IsLeaf H b ∧
        ((a = 1 ∧ orientation' b = true) ∨
         (a = 2 ∧ orientation' b = false))) := by
      rw [hBefore b hb]
    _ ↔ (finiteTwoBlockCarrier H K n m orientation').edge
        a b (rightBlockImage n v) :=
      (finiteTwoBlockCarrier_right_leaf_column_iff
        FH FK hshape orientation' a b v
        hab hbn hv3 hvm hvLeaf).symm

/-- CORE NONCIRCULARITY FOR ACTUAL ORDERED SUMS. The comparison
of a fixed left vertex u with a right leaf is independent of the
orientation bit at u itself and all later bits. Only earlier bits
can influence it. -/
theorem finiteTwoBlockCarrier_lex_prefix_independent
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hshape : ∀ a b c : Nat, K.edge a b c →
      PermittedDiaryEdge K a b c)
    (orientation orientation' : Nat → Bool)
    (u v : Nat) (hu : u < n)
    (hv3 : 3 ≤ v) (hvm : v < m) (hvLeaf : IsLeaf K v)
    (hBefore : ∀ t : Nat, t < u → orientation t = orientation' t) :
    (LexEarlier (finiteTwoBlockCarrier H K n m orientation)
         u (rightBlockImage n v) ↔
      LexEarlier (finiteTwoBlockCarrier H K n m orientation')
         u (rightBlockImage n v)) := by
  have huv : u < rightBlockImage n v := by
    have hge := rightBlockImage_nonmarker_ge n v
      FH.length_ge_three hv3
    omega
  have hLeft :
      ∀ a b : Nat, a < b → b < u →
        ((finiteTwoBlockCarrier H K n m orientation).edge a b u ↔
         (finiteTwoBlockCarrier H K n m orientation').edge a b u) := by
    intro a b _hab _hb
    calc
      (finiteTwoBlockCarrier H K n m orientation).edge a b u ↔
          H.edge a b u :=
        finiteTwoBlockCarrier_left_edge_iff
          FH FK orientation a b u hu
      _ ↔ (finiteTwoBlockCarrier H K n m orientation').edge a b u :=
        (finiteTwoBlockCarrier_left_edge_iff
          FH FK orientation' a b u hu).symm
  have hRight :=
    finiteTwoBlockCarrier_right_column_prefix_congr
      FH FK hshape orientation orientation' u v hu
      hv3 hvm hvLeaf hBefore
  exact lexEarlier_prefix_congr_of_edge_columns
    (H := finiteTwoBlockCarrier H K n m orientation)
    (K := finiteTwoBlockCarrier H K n m orientation')
    u (rightBlockImage n v) huv hLeft hRight

end DiaryLeafPriority
end ThreeUniformDiaries
