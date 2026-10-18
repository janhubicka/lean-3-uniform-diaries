import ThreeUniformDiaries.DiaryFiniteOrderedSumCarrier

/-!
# Exact left-block type preservation in finite ordered sums

Unlike the translated right block, the left block is a literal
initial segment of the combined edge table. The induced-copy
theorem already says that every edge whose third vertex is
in the left block is preserved AND reflected.

Consequently singleton types and full ordered-pair types on any
original left vertices agree at EVERY cut, not only cuts inside
the left block. This supplies the type-transport input to V1/V2
coherence for positive splits in the left block.

No source or target V/E/S axioms and no choice of cross Devlin
orientations are needed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- The actual finite ordered sum preserves AND reflects all
singleton prefix comparisons of original left-block vertices.
The type cut can even lie beyond the original left block. -/
theorem finiteTwoBlockCarrier_left_oneType_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (l u v : Nat) (hu : u < n) (hv : v < n) :
    ((finiteTwoBlockCarrier H K n m bits).SameOneTypeBelow l u v ↔
      H.SameOneTypeBelow l u v) := by
  constructor
  · intro hTarget a b hab hb
    have heU := finiteTwoBlockCarrier_left_edge_iff
      FH FK bits a b u hu
    have heV := finiteTwoBlockCarrier_left_edge_iff
      FH FK bits a b v hv
    exact heU.symm.trans
      ((hTarget (a := a) (b := b) hab hb).trans heV)
  · intro hSource a b hab hb
    have heU := finiteTwoBlockCarrier_left_edge_iff
      FH FK bits a b u hu
    have heV := finiteTwoBlockCarrier_left_edge_iff
      FH FK bits a b v hv
    exact heU.trans
      ((hSource (a := a) (b := b) hab hb).trans heV.symm)

/-- Auxiliary pair-type comparisons on left vertices are
unchanged at arbitrary cuts, including cuts in the right block. -/
theorem finiteTwoBlockCarrier_left_auxType_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (l a b c d : Nat) (hb : b < n) (hd : d < n) :
    ((finiteTwoBlockCarrier H K n m bits).SameAuxTypeBelow
        l a b c d ↔ H.SameAuxTypeBelow l a b c d) := by
  constructor
  · intro hTarget x hx
    have heAB := finiteTwoBlockCarrier_left_edge_iff
      FH FK bits x a b hb
    have heCD := finiteTwoBlockCarrier_left_edge_iff
      FH FK bits x c d hd
    exact heAB.symm.trans ((hTarget (a := x) hx).trans heCD)
  · intro hSource x hx
    have heAB := finiteTwoBlockCarrier_left_edge_iff
      FH FK bits x a b hb
    have heCD := finiteTwoBlockCarrier_left_edge_iff
      FH FK bits x c d hd
    exact heAB.trans ((hSource (a := x) hx).trans heCD.symm)

/-- Exact FULL two-type comparison transport on original left
vertices, at arbitrary cut levels. This does not require leaf
roles or ordered pairs. -/
theorem finiteTwoBlockCarrier_left_twoType_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (l a b c d : Nat)
    (ha : a < n) (hb : b < n) (hc : c < n) (hd : d < n) :
    ((finiteTwoBlockCarrier H K n m bits).SameTwoTypeBelow
        l a b c d ↔ H.SameTwoTypeBelow l a b c d) := by
  have hFirst := finiteTwoBlockCarrier_left_oneType_iff
    FH FK bits l a c ha hc
  have hSecond := finiteTwoBlockCarrier_left_oneType_iff
    FH FK bits l b d hb hd
  have hAux := finiteTwoBlockCarrier_left_auxType_iff
    FH FK bits l a b c d hb hd
  exact and_congr hFirst (and_congr hSecond hAux)

end DiaryLeafPriority
end ThreeUniformDiaries
