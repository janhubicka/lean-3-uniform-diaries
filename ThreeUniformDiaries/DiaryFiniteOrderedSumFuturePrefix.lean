import ThreeUniformDiaries.DiaryFiniteOrderedSumCarrier
import ThreeUniformDiaries.DiaryLexFutureLeafLocality

/-!
# Uniform future-leaf types across a finite ordered sum

Consider the raw two-block diary carrier with induced internal
copies and only cross Devlin marker edges. If the right finite
edge table has the manuscript E1--E5 permitted-edge shapes,
then EVERY two right-block leaves have identical singleton
types below ANY left-block vertex.

The right source can have arbitrary internal normal edges and
split incidences; they lie too late to affect this prefix.
Among tests whose middle coordinate belongs to the left block,
the only possible nonzero tests are cross Devlin marker bits,
chosen uniformly for all later right leaves.

Combining this with the separately verified LexEarlier locality
theorem proves that an earlier leaf has ONE common lexicographic
orientation toward the entire right block. This checks the
uniformity clause needed for V3, but not yet the existence of a
globally consistent orientation schedule.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- In an E-shaped finite diary frame, an actual leaf cannot
receive any edge whose middle coordinate is below marker cut 3.
This uses permitted edge SHAPES, not S1/S2 or V1/V2 witnesses. -/
theorem finiteFrame_leaf_no_early_middle
    (K : Ordered3Graph Nat)
    (hshape : ∀ a b c : Nat, K.edge a b c →
      PermittedDiaryEdge K a b c)
    (a b v : Nat)
    (hab : a < b) (hb3 : b < 3) (hv : IsLeaf K v) :
    ¬ K.edge a b v := by
  intro he
  rcases hshape a b v he with
      hMarker | hOne | hTwo | hDevlin | hNormal
  · rcases hMarker.2.1 with hb1 | hb2
    · have hbit : K.edge 0 1 v := by
        simpa only [hMarker.1, hb1] using he
      exact hv.2.1 hbit
    · have hbit : K.edge 0 2 v := by
        simpa only [hMarker.1, hb2] using he
      exact hv.2.2 hbit
  · have hge := hOne.2.1.1
    omega
  · have hge := hTwo.1.1
    omega
  · have hge := hDevlin.2.1.1
    omega
  · have hge := hNormal.1.1
    omega

/-- Every test with middle coordinate in the left block and
terminal at an actual right leaf has precisely the cross-marker
shape, with bit determined by the middle left leaf. The formula
is independent of WHICH right leaf is used. -/
theorem finiteTwoBlockCarrier_right_leaf_column_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hshape : ∀ a b c : Nat, K.edge a b c →
      PermittedDiaryEdge K a b c)
    (orientation : Nat → Bool)
    (a b v : Nat)
    (hab : a < b) (hbn : b < n)
    (hv3 : 3 ≤ v) (hvm : v < m) (hvLeaf : IsLeaf K v) :
    (finiteTwoBlockCarrier H K n m orientation).edge
       a b (rightBlockImage n v) ↔
       3 ≤ b ∧ IsLeaf H b ∧
          ((a = 1 ∧ orientation b = true) ∨
           (a = 2 ∧ orientation b = false)) := by
  constructor
  · intro he
    rcases he with hLeft | hRight | hCross
    · have hge := rightBlockImage_nonmarker_ge n v
        FH.length_ge_three hv3
      omega
    · obtain ⟨a',b',c',hK,_hcm,ha,hb,hc⟩ := hRight
      have hinj :=
        (rightBlockImage_strictMono n FH.length_ge_three).injective
      have hcv : c' = v := (hinj hc).symm
      subst c'
      have hbSmall : b' < 3 := by
        by_contra hbad
        have hbge : 3 ≤ b' := by omega
        have hge := rightBlockImage_nonmarker_ge n b'
          FH.length_ge_three hbge
        omega
      have habK : a' < b' :=
        (FK.edge_support a' b' v hK).1
      exact False.elim
        (finiteFrame_leaf_no_early_middle K hshape
          a' b' v habK hbSmall hvLeaf hK)
    · obtain ⟨u,v',hu3,hun,hlu,_hv3,_hvm,_hlv,hy,_hz,hbit⟩ := hCross
      have hEq : u = b := hy.symm
      subst u
      exact ⟨hu3, hlu, hbit⟩
  · rintro ⟨hb3,hbLeaf,hbit⟩
    exact Or.inr (Or.inr
      ⟨b,v,hb3,hbn,hbLeaf,hv3,hvm,hvLeaf,rfl,rfl,hbit⟩)

/-- All later right-block leaves have IDENTICAL singleton prefix
types at every cut strictly before the end of the left block. -/
theorem finiteTwoBlockCarrier_right_leaves_uniform_below_left
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hshape : ∀ a b c : Nat, K.edge a b c →
      PermittedDiaryEdge K a b c)
    (orientation : Nat → Bool)
    (u v w : Nat) (hu : u ≤ n)
    (hv3 : 3 ≤ v) (hvm : v < m) (hvLeaf : IsLeaf K v)
    (hw3 : 3 ≤ w) (hwm : w < m) (hwLeaf : IsLeaf K w) :
    (finiteTwoBlockCarrier H K n m orientation).SameOneTypeBelow u
      (rightBlockImage n v) (rightBlockImage n w) := by
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
    _ ↔ (finiteTwoBlockCarrier H K n m orientation).edge
        a b (rightBlockImage n w) :=
      (finiteTwoBlockCarrier_right_leaf_column_iff
        FH FK hshape orientation a b w hab hbn hw3 hwm hwLeaf).symm

/-- A genuine left leaf has the SAME literal LexEarlier
orientation toward every right leaf, regardless of the
Boolean orientation assignment or the internal right edges.
This is exactly the consistency reduction needed for cross V3. -/
theorem finiteTwoBlockCarrier_left_leaf_lex_uniform
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hshape : ∀ a b c : Nat, K.edge a b c →
      PermittedDiaryEdge K a b c)
    (orientation : Nat → Bool)
    (u v w : Nat) (hu3 : 3 ≤ u) (hun : u < n)
    (hv3 : 3 ≤ v) (hvm : v < m) (hvLeaf : IsLeaf K v)
    (hw3 : 3 ≤ w) (hwm : w < m) (hwLeaf : IsLeaf K w) :
    LexEarlier (finiteTwoBlockCarrier H K n m orientation)
        u (rightBlockImage n v) ↔
      LexEarlier (finiteTwoBlockCarrier H K n m orientation)
        u (rightBlockImage n w) := by
  have huv : u < rightBlockImage n v := by
    have hge := rightBlockImage_nonmarker_ge n v
      FH.length_ge_three hv3
    omega
  have huw : u < rightBlockImage n w := by
    have hge := rightBlockImage_nonmarker_ge n w
      FH.length_ge_three hw3
    omega
  exact lexEarlier_right_congr_of_sameOneTypeBelow
    (finiteTwoBlockCarrier H K n m orientation)
    u (rightBlockImage n v) (rightBlockImage n w)
    huv huw
    (finiteTwoBlockCarrier_right_leaves_uniform_below_left
      FH FK hshape orientation u v w hun.le
      hv3 hvm hvLeaf hw3 hwm hwLeaf)

/-- Consequently ONE representative right leaf suffices to
check cross V3-marker 1 toward ALL right leaves from the left
vertex u. This is a reduction, not an existence theorem for
a globally coherent marker schedule. -/
theorem finiteTwoBlockCarrier_cross_V3_one_of_representative
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hshape : ∀ a b c : Nat, K.edge a b c →
      PermittedDiaryEdge K a b c)
    (orientation : Nat → Bool)
    (u v0 : Nat) (hu3 : 3 ≤ u) (hun : u < n)
    (huLeaf : IsLeaf H u)
    (hv03 : 3 ≤ v0) (hv0m : v0 < m)
    (hv0Leaf : IsLeaf K v0)
    (hRepresentative :
      (orientation u = true) ↔
        LexEarlier (finiteTwoBlockCarrier H K n m orientation)
          u (rightBlockImage n v0)) :
    ∀ v : Nat, 3 ≤ v → v < m → IsLeaf K v →
      ((finiteTwoBlockCarrier H K n m orientation).edge
          1 u (rightBlockImage n v) ↔
        LexEarlier (finiteTwoBlockCarrier H K n m orientation)
          u (rightBlockImage n v)) := by
  intro v hv3 hvm hvLeaf
  calc
    (finiteTwoBlockCarrier H K n m orientation).edge
        1 u (rightBlockImage n v) ↔ orientation u = true :=
      finiteTwoBlockCarrier_cross_marker_one
        FH FK orientation u v hu3 hun huLeaf hv3 hvm hvLeaf
    _ ↔ LexEarlier (finiteTwoBlockCarrier H K n m orientation)
        u (rightBlockImage n v0) := hRepresentative
    _ ↔ LexEarlier (finiteTwoBlockCarrier H K n m orientation)
        u (rightBlockImage n v) :=
      (finiteTwoBlockCarrier_left_leaf_lex_uniform
        FH FK hshape orientation u v0 v hu3 hun
        hv03 hv0m hv0Leaf hv3 hvm hvLeaf)

end DiaryLeafPriority
end ThreeUniformDiaries
