import ThreeUniformDiaries.DiaryLexPrefixEdgeInvariance
import ThreeUniformDiaries.DiaryFiniteOrderedSumRoles

/-!
# Internal left-block V3 preservation in finite ordered sums

Every edge with third vertex below the end of the left finite
block is copied and reflected literally. The checked generic
lexicographic prefix-invariance theorem therefore makes
LexEarlier on two left leaves identical to the source comparison,
even when arbitrary cross Devlin markers have been inserted.

Thus the entire source V3 marker-1/marker-2 specification transfers
to left-left leaf pairs inside the actual carrier. This part
needs no choice of cross bits and does not establish right-right
or cross-copy V3, or V1/V2 coherence.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- Literal lexicographic order of two original left vertices
is unaffected by the addition of the second block and all
cross-copy edges, since both deciding singleton columns end
at vertices strictly below n. -/
theorem finiteTwoBlockCarrier_left_LexEarlier_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (u v : Nat) (huv : u < v) (hvn : v < n) :
    LexEarlier H u v ↔
      LexEarlier (finiteTwoBlockCarrier H K n m bits) u v := by
  have hun : u < n := by omega
  have hX :
      ∀ a b : Nat, a < b → b < u →
        (H.edge a b u ↔
          (finiteTwoBlockCarrier H K n m bits).edge a b u) := by
    intro a b _ _
    exact (finiteTwoBlockCarrier_left_edge_iff
      FH FK bits a b u hun).symm
  have hY :
      ∀ a b : Nat, a < b → b < u →
        (H.edge a b v ↔
          (finiteTwoBlockCarrier H K n m bits).edge a b v) := by
    intro a b _ _
    exact (finiteTwoBlockCarrier_left_edge_iff
      FH FK bits a b v hvn).symm
  exact lexEarlier_prefix_congr_of_edge_columns
    (H := H) (K := finiteTwoBlockCarrier H K n m bits)
    u v huv hX hY

/-- Both internal left-block V3 marker clauses transport exactly,
as soon as the ORIGINAL left leaf pairs satisfy the two source
marker clauses. No cross-copy orientation assumption is required. -/
theorem finiteTwoBlockCarrier_left_V3
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (hV3one : ∀ a b : Nat, a < b → b < n →
      IsLeaf H a → IsLeaf H b →
      (H.edge 1 a b ↔ LexEarlier H a b))
    (hV3two : ∀ a b : Nat, a < b → b < n →
      IsLeaf H a → IsLeaf H b →
      (H.edge 2 a b ↔ ¬ LexEarlier H a b)) :
    ∀ u v : Nat, u < v → v < n →
      IsLeaf (finiteTwoBlockCarrier H K n m bits) u →
      IsLeaf (finiteTwoBlockCarrier H K n m bits) v →
      (((finiteTwoBlockCarrier H K n m bits).edge 1 u v ↔
          LexEarlier (finiteTwoBlockCarrier H K n m bits) u v) ∧
       ((finiteTwoBlockCarrier H K n m bits).edge 2 u v ↔
          ¬ LexEarlier (finiteTwoBlockCarrier H K n m bits) u v)) := by
  intro u v huv hvn hu hv
  have hun : u < n := by omega
  have hULeaf : IsLeaf H u :=
    (finiteTwoBlockCarrier_left_leaf_iff FH FK bits u hun).mp hu
  have hVLeaf : IsLeaf H v :=
    (finiteTwoBlockCarrier_left_leaf_iff FH FK bits v hvn).mp hv
  have hLex := finiteTwoBlockCarrier_left_LexEarlier_iff
    FH FK bits u v huv hvn
  constructor
  · calc
      (finiteTwoBlockCarrier H K n m bits).edge 1 u v ↔
          H.edge 1 u v :=
        finiteTwoBlockCarrier_left_edge_iff FH FK bits 1 u v hvn
      _ ↔ LexEarlier H u v :=
        hV3one u v huv hvn hULeaf hVLeaf
      _ ↔ LexEarlier (finiteTwoBlockCarrier H K n m bits) u v :=
        hLex
  · calc
      (finiteTwoBlockCarrier H K n m bits).edge 2 u v ↔
          H.edge 2 u v :=
        finiteTwoBlockCarrier_left_edge_iff FH FK bits 2 u v hvn
      _ ↔ ¬ LexEarlier H u v :=
        hV3two u v huv hvn hULeaf hVLeaf
      _ ↔ ¬ LexEarlier (finiteTwoBlockCarrier H K n m bits) u v :=
        not_congr hLex

end DiaryLeafPriority
end ThreeUniformDiaries
