import ThreeUniformDiaries.DiaryFiniteOrderedSumRoleCases
import ThreeUniformDiaries.DiaryFiniteOrderedSumLeftCoherence
import ThreeUniformDiaries.DiaryFiniteOrderedSumRightGlobalCoherence

/-!
# Global V1/V2 positive coherence and role validity of finite sums

The finite ordered sum was checked separately inside its two blocks:
left positive classes cannot acquire external witnesses; right
positive classes recover all source right endpoints. These facts
prove genuine V1/V2 coherence for ALL positive target leaf classes,
not merely named source images.

Exhaustive bounded vertex-role classification shows every target
split belongs to one of those blocks, so the casewise proofs
assemble into the complete finite V1/V2 coherence statements.

The same classification transports the three marker-defined
vertex roles over the entire bounded sum. Orientation bits are
arbitrary: cross Devlin marker choices do not affect these clauses.

Finite V3 and finite split witnesses are independent obligations.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- Every nonmarker vertex in the finite combined frame receives
one of the three true target marker roles, provided both source
finite blocks have exhaustive bounded role coverage. -/
theorem finiteTwoBlockCarrier_role_valid
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hH : ∀ z : Nat, 3 ≤ z → z < n →
      IsLeaf H z ∨ IsOneSplit H z ∨ IsTwoSplit H z)
    (hK : ∀ z : Nat, 3 ≤ z → z < m →
      IsLeaf K z ∨ IsOneSplit K z ∨ IsTwoSplit K z)
    (bits : Nat → Bool)
    (z : Nat) (hz3 : 3 ≤ z)
    (hzBound : z < finiteTwoBlockLength n m) :
    IsLeaf (finiteTwoBlockCarrier H K n m bits) z ∨
      IsOneSplit (finiteTwoBlockCarrier H K n m bits) z ∨
      IsTwoSplit (finiteTwoBlockCarrier H K n m bits) z := by
  rcases finiteTwoBlock_nonmarker_cases
    FH.length_ge_three FK.length_ge_three z hz3 hzBound with
      hLeft | ⟨v,hv3,hvm,hImage⟩
  · rcases hH z hz3 hLeft with hLeaf | hOne | hTwo
    · exact Or.inl
        ((finiteTwoBlockCarrier_left_leaf_iff
          FH FK bits z hLeft).mpr hLeaf)
    · exact Or.inr (Or.inl
        ((finiteTwoBlockCarrier_left_oneSplit_iff
          FH FK bits z hLeft).mpr hOne))
    · exact Or.inr (Or.inr
        ((finiteTwoBlockCarrier_left_twoSplit_iff
          FH FK bits z hLeft).mpr hTwo))
  · subst z
    rcases hK v hv3 hvm with hLeaf | hOne | hTwo
    · exact Or.inl
        ((finiteTwoBlockCarrier_right_leaf_iff
          FH FK bits v hv3 hvm).mpr hLeaf)
    · exact Or.inr (Or.inl
        ((finiteTwoBlockCarrier_right_oneSplit_iff
          FH FK bits v hv3 hvm).mpr hOne))
    · exact Or.inr (Or.inr
        ((finiteTwoBlockCarrier_right_twoSplit_iff
          FH FK bits v hv3 hvm).mpr hTwo))

/-- Full actual V1 positive-class coherence at any target
one-split. All positive target leaves are unrestricted. -/
theorem finiteTwoBlockCarrier_oneSplit_coherent
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hV1H : ∀ s a b : Nat,
      IsOneSplit H s → IsLeaf H a → IsLeaf H b →
      H.edge 0 s a → H.edge 0 s b →
      H.SameOneTypeBelow s a b)
    (hEK : ∀ x y z : Nat, K.edge x y z →
      PermittedDiaryEdge K x y z)
    (hV1K : ∀ s a b : Nat,
      IsOneSplit K s → IsLeaf K a → IsLeaf K b →
      K.edge 0 s a → K.edge 0 s b →
      K.SameOneTypeBelow s a b)
    (bits : Nat → Bool)
    (s a b : Nat)
    (hs : IsOneSplit (finiteTwoBlockCarrier H K n m bits) s)
    (ha : IsLeaf (finiteTwoBlockCarrier H K n m bits) a)
    (hb : IsLeaf (finiteTwoBlockCarrier H K n m bits) b)
    (hA : (finiteTwoBlockCarrier H K n m bits).edge 0 s a)
    (hB : (finiteTwoBlockCarrier H K n m bits).edge 0 s b) :
    (finiteTwoBlockCarrier H K n m bits).SameOneTypeBelow s a b := by
  have hBound : s < finiteTwoBlockLength n m :=
    ((finiteTwoBlockCarrier_finiteFrame FH FK bits).edge_support
      0 1 s hs.2.1).2.2.2
  rcases finiteTwoBlock_oneSplit_cases FH FK bits s hs hBound with
      ⟨hsn,_hsSource⟩ | ⟨v,hv3,hvm,_hvSource,hImage⟩
  · exact finiteTwoBlockCarrier_left_oneSplit_coherent
      FH FK hV1H bits s a b hs.1 hsn hs ha hb hA hB
  · subst s
    exact finiteTwoBlockCarrier_right_oneSplit_coherent_all
      FH FK hEK hV1K bits v a b hv3 hvm hs ha hb hA hB

/-- Full actual V2 positive-class coherence at any target
two-split, for all ordered target leaf pairs with positive edges. -/
theorem finiteTwoBlockCarrier_twoSplit_coherent
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hV2H : ∀ s a b c d : Nat,
      IsTwoSplit H s → a < b → c < d →
      IsLeaf H a → IsLeaf H b → IsLeaf H c → IsLeaf H d →
      H.edge s a b → H.edge s c d →
      H.SameTwoTypeBelow s a b c d)
    (hEK : ∀ x y z : Nat, K.edge x y z →
      PermittedDiaryEdge K x y z)
    (hV2K : ∀ s a b c d : Nat,
      IsTwoSplit K s → a < b → c < d →
      IsLeaf K a → IsLeaf K b → IsLeaf K c → IsLeaf K d →
      K.edge s a b → K.edge s c d →
      K.SameTwoTypeBelow s a b c d)
    (bits : Nat → Bool)
    (s a b c d : Nat)
    (hs : IsTwoSplit (finiteTwoBlockCarrier H K n m bits) s)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf (finiteTwoBlockCarrier H K n m bits) a)
    (hb : IsLeaf (finiteTwoBlockCarrier H K n m bits) b)
    (hc : IsLeaf (finiteTwoBlockCarrier H K n m bits) c)
    (hd : IsLeaf (finiteTwoBlockCarrier H K n m bits) d)
    (hAB : (finiteTwoBlockCarrier H K n m bits).edge s a b)
    (hCD : (finiteTwoBlockCarrier H K n m bits).edge s c d) :
    (finiteTwoBlockCarrier H K n m bits).SameTwoTypeBelow
      s a b c d := by
  have hBound : s < finiteTwoBlockLength n m :=
    ((finiteTwoBlockCarrier_finiteFrame FH FK bits).edge_support
      0 2 s hs.2.2).2.2.2
  rcases finiteTwoBlock_twoSplit_cases FH FK bits s hs hBound with
      ⟨hsn,_hsSource⟩ | ⟨v,hv3,hvm,_hvSource,hImage⟩
  · exact finiteTwoBlockCarrier_left_twoSplit_coherent
      FH FK hV2H bits s a b c d hs.1 hsn
      hab hcd hs ha hb hc hd hAB hCD
  · subst s
    exact finiteTwoBlockCarrier_right_twoSplit_coherent_all
      FH FK hEK hV2K bits v a b c d hv3 hvm
      hab hcd hs ha hb hc hd hAB hCD

end DiaryLeafPriority
end ThreeUniformDiaries
