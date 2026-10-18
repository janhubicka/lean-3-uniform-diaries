import ThreeUniformDiaries.DiaryFiniteOrderedSumRightPositiveSupport

/-!
# Global V1/V2 coherence at right-block splits

The previous right-block coherence proofs considered positive leaves
and pairs already presented as images of source right leaves. We now
remove that restriction: the support lemmas recover source right
vertices from ANY actual positive target edge incident with a right
split. No extra positive class can come from a left or cross edge.

Thus both right-split coherence clauses hold with unrestricted target
leaf variables, whenever the finite source has the respective V1/V2
coherence axiom. Arbitrary cross orientation bits remain allowed.

This does NOT claim the split witness axioms, right-right V3,
or a global infinite RolePrediary on the finite carrier.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- Full positive-class V1 coherence for any original right
one-split, quantified over ALL positive target leaf vertices. -/
theorem finiteTwoBlockCarrier_right_oneSplit_coherent_all
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hshape : ∀ x y z : Nat, K.edge x y z →
      PermittedDiaryEdge K x y z)
    (hV1 : ∀ s a b : Nat,
      IsOneSplit K s → IsLeaf K a → IsLeaf K b →
      K.edge 0 s a → K.edge 0 s b →
      K.SameOneTypeBelow s a b)
    (bits : Nat → Bool)
    (s a b : Nat) (hs3 : 3 ≤ s) (hsm : s < m)
    (hSplit : IsOneSplit (finiteTwoBlockCarrier H K n m bits)
      (rightBlockImage n s))
    (haLeaf : IsLeaf (finiteTwoBlockCarrier H K n m bits) a)
    (hbLeaf : IsLeaf (finiteTwoBlockCarrier H K n m bits) b)
    (haPos : (finiteTwoBlockCarrier H K n m bits).edge
      0 (rightBlockImage n s) a)
    (hbPos : (finiteTwoBlockCarrier H K n m bits).edge
      0 (rightBlockImage n s) b) :
    (finiteTwoBlockCarrier H K n m bits).SameOneTypeBelow
      (rightBlockImage n s) a b := by
  obtain ⟨u,hum,hau,hSourceU⟩ :=
    finiteTwoBlockCarrier_right_oneSplit_positive_source
      FH FK bits s a hs3 hsm haPos
  obtain ⟨v,hvm,hbv,hSourceV⟩ :=
    finiteTwoBlockCarrier_right_oneSplit_positive_source
      FH FK bits s b hs3 hsm hbPos
  subst a
  subst b
  have hu3 : 3 ≤ u := by
    have he := FK.edge_support 0 s u hSourceU
    omega
  have hv3 : 3 ≤ v := by
    have he := FK.edge_support 0 s v hSourceV
    omega
  have huLeaf : IsLeaf K u :=
    (finiteTwoBlockCarrier_right_leaf_iff
      FH FK bits u hu3 hum).mp haLeaf
  have hvLeaf : IsLeaf K v :=
    (finiteTwoBlockCarrier_right_leaf_iff
      FH FK bits v hv3 hvm).mp hbLeaf
  exact finiteTwoBlockCarrier_right_oneSplit_coherent
    FH FK hshape hV1 bits s u v hs3 hsm
    hu3 hum huLeaf hv3 hvm hvLeaf hSplit haPos hbPos

/-- Full positive-class V2 coherence for any original right
two-split, quantified over ALL positive target ordered leaf pairs. -/
theorem finiteTwoBlockCarrier_right_twoSplit_coherent_all
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hshape : ∀ x y z : Nat, K.edge x y z →
      PermittedDiaryEdge K x y z)
    (hV2 : ∀ s a b c d : Nat,
      IsTwoSplit K s → a < b → c < d →
      IsLeaf K a → IsLeaf K b → IsLeaf K c → IsLeaf K d →
      K.edge s a b → K.edge s c d →
      K.SameTwoTypeBelow s a b c d)
    (bits : Nat → Bool)
    (s a b c d : Nat) (hs3 : 3 ≤ s) (hsm : s < m)
    (hab : a < b) (hcd : c < d)
    (hSplit : IsTwoSplit (finiteTwoBlockCarrier H K n m bits)
      (rightBlockImage n s))
    (haLeaf : IsLeaf (finiteTwoBlockCarrier H K n m bits) a)
    (hbLeaf : IsLeaf (finiteTwoBlockCarrier H K n m bits) b)
    (hcLeaf : IsLeaf (finiteTwoBlockCarrier H K n m bits) c)
    (hdLeaf : IsLeaf (finiteTwoBlockCarrier H K n m bits) d)
    (hAB : (finiteTwoBlockCarrier H K n m bits).edge
      (rightBlockImage n s) a b)
    (hCD : (finiteTwoBlockCarrier H K n m bits).edge
      (rightBlockImage n s) c d) :
    (finiteTwoBlockCarrier H K n m bits).SameTwoTypeBelow
      (rightBlockImage n s) a b c d := by
  obtain ⟨u,v,hum,hvm,hau,hbv,hSourceUV⟩ :=
    finiteTwoBlockCarrier_right_twoSplit_positive_source
      FH FK bits s a b hs3 hsm hAB
  obtain ⟨w,z,hwm,hzm,hcw,hdz,hSourceWZ⟩ :=
    finiteTwoBlockCarrier_right_twoSplit_positive_source
      FH FK bits s c d hs3 hsm hCD
  subst a
  subst b
  subst c
  subst d
  have heUV := FK.edge_support s u v hSourceUV
  have heWZ := FK.edge_support s w z hSourceWZ
  have hu3 : 3 ≤ u := by omega
  have hv3 : 3 ≤ v := by omega
  have hw3 : 3 ≤ w := by omega
  have hz3 : 3 ≤ z := by omega
  have huLeaf : IsLeaf K u :=
    (finiteTwoBlockCarrier_right_leaf_iff
      FH FK bits u hu3 hum).mp haLeaf
  have hvLeaf : IsLeaf K v :=
    (finiteTwoBlockCarrier_right_leaf_iff
      FH FK bits v hv3 hvm).mp hbLeaf
  have hwLeaf : IsLeaf K w :=
    (finiteTwoBlockCarrier_right_leaf_iff
      FH FK bits w hw3 hwm).mp hcLeaf
  have hzLeaf : IsLeaf K z :=
    (finiteTwoBlockCarrier_right_leaf_iff
      FH FK bits z hz3 hzm).mp hdLeaf
  exact finiteTwoBlockCarrier_right_twoSplit_coherent
    FH FK hshape hV2 bits s u v w z hs3 hsm
    hu3 hum huLeaf hv3 hvm hvLeaf
    hw3 hwm hwLeaf hz3 hzm hzLeaf
    heUV.2.1 heWZ.2.1 hSplit hAB hCD

end DiaryLeafPriority
end ThreeUniformDiaries
