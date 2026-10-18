import ThreeUniformDiaries.DiaryFiniteOrderedSumRightPairTransport
import ThreeUniformDiaries.DiaryFiniteOrderedSumRoles

/-!
# V1/V2 positive-class coherence in the right block of a finite sum

The right-block type transports make the two coherence obligations
almost formal consequences of the original right finite diary data.

For V1, a positive one-split and two positively incident right leaves
are pulled back by the induced right embedding. Source V1 gives the
singleton type equality, which is then transported to the actual
target cut. The marker-defined target split role is reflected.

For V2 the same argument uses the full ordered-pair two-type
transport. Both proofs are independent of the cross orientation bits.

These are the RIGHT-BLOCK coherence cases only. The proofs do not
claim V1/V2 witnesses, right-right V3, left-block coherence, or the
full pre-diary statement.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- Genuine target V1 coherence for an original right one-split
and two original right leaves, assuming only the corresponding
finite source V1 coherence clause. All positive incidences and
the split role are read in the ACTUAL raw target. -/
theorem finiteTwoBlockCarrier_right_oneSplit_coherent
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hshape : ∀ a b c : Nat, K.edge a b c →
      PermittedDiaryEdge K a b c)
    (hV1 : ∀ s a b : Nat,
      IsOneSplit K s → IsLeaf K a → IsLeaf K b →
      K.edge 0 s a → K.edge 0 s b →
      K.SameOneTypeBelow s a b)
    (bits : Nat → Bool)
    (s a b : Nat) (hs3 : 3 ≤ s) (hsm : s < m)
    (ha3 : 3 ≤ a) (ham : a < m) (haLeaf : IsLeaf K a)
    (hb3 : 3 ≤ b) (hbm : b < m) (hbLeaf : IsLeaf K b)
    (hSplit :
      IsOneSplit (finiteTwoBlockCarrier H K n m bits)
        (rightBlockImage n s))
    (hA : (finiteTwoBlockCarrier H K n m bits).edge
      0 (rightBlockImage n s) (rightBlockImage n a))
    (hB : (finiteTwoBlockCarrier H K n m bits).edge
      0 (rightBlockImage n s) (rightBlockImage n b)) :
    (finiteTwoBlockCarrier H K n m bits).SameOneTypeBelow
      (rightBlockImage n s)
      (rightBlockImage n a) (rightBlockImage n b) := by
  have hSourceSplit : IsOneSplit K s :=
    (finiteTwoBlockCarrier_right_oneSplit_iff
      FH FK bits s hs3 hsm).mp hSplit
  have hZero : rightBlockImage n 0 = 0 :=
    rightBlockImage_marker n 0 (by omega)
  have hSourceA : K.edge 0 s a :=
    (finiteTwoBlockCarrier_right_edge_iff_all
      FH FK bits 0 s a).mp
      (by simpa only [hZero] using hA)
  have hSourceB : K.edge 0 s b :=
    (finiteTwoBlockCarrier_right_edge_iff_all
      FH FK bits 0 s b).mp
      (by simpa only [hZero] using hB)
  exact (finiteTwoBlockCarrier_right_leaf_oneType_iff
    FH FK hshape bits s a b hs3
    ha3 ham haLeaf hb3 hbm hbLeaf).mpr
      (hV1 s a b hSourceSplit haLeaf hbLeaf hSourceA hSourceB)

/-- Genuine target V2 coherence for an original right two-split
and two positively incident ordered leaf pairs. The target
hypotheses are literal edges and marker-defined roles; all
type comparisons are the actual full ordered pair types. -/
theorem finiteTwoBlockCarrier_right_twoSplit_coherent
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hshape : ∀ a b c : Nat, K.edge a b c →
      PermittedDiaryEdge K a b c)
    (hV2 : ∀ s a b c d : Nat,
      IsTwoSplit K s → a < b → c < d →
      IsLeaf K a → IsLeaf K b → IsLeaf K c → IsLeaf K d →
      K.edge s a b → K.edge s c d →
      K.SameTwoTypeBelow s a b c d)
    (bits : Nat → Bool)
    (s a b c d : Nat) (hs3 : 3 ≤ s) (hsm : s < m)
    (ha3 : 3 ≤ a) (ham : a < m) (haLeaf : IsLeaf K a)
    (hb3 : 3 ≤ b) (hbm : b < m) (hbLeaf : IsLeaf K b)
    (hc3 : 3 ≤ c) (hcm : c < m) (hcLeaf : IsLeaf K c)
    (hd3 : 3 ≤ d) (hdm : d < m) (hdLeaf : IsLeaf K d)
    (hab : a < b) (hcd : c < d)
    (hSplit :
      IsTwoSplit (finiteTwoBlockCarrier H K n m bits)
        (rightBlockImage n s))
    (hAB : (finiteTwoBlockCarrier H K n m bits).edge
      (rightBlockImage n s) (rightBlockImage n a)
      (rightBlockImage n b))
    (hCD : (finiteTwoBlockCarrier H K n m bits).edge
      (rightBlockImage n s) (rightBlockImage n c)
      (rightBlockImage n d)) :
    (finiteTwoBlockCarrier H K n m bits).SameTwoTypeBelow
      (rightBlockImage n s)
      (rightBlockImage n a) (rightBlockImage n b)
      (rightBlockImage n c) (rightBlockImage n d) := by
  have hSourceSplit : IsTwoSplit K s :=
    (finiteTwoBlockCarrier_right_twoSplit_iff
      FH FK bits s hs3 hsm).mp hSplit
  have hSourceAB : K.edge s a b :=
    (finiteTwoBlockCarrier_right_edge_iff_all
      FH FK bits s a b).mp hAB
  have hSourceCD : K.edge s c d :=
    (finiteTwoBlockCarrier_right_edge_iff_all
      FH FK bits s c d).mp hCD
  exact (finiteTwoBlockCarrier_right_leaf_twoType_iff
    FH FK hshape bits s a b c d hs3
    ha3 ham haLeaf hb3 hbm hbLeaf
    hc3 hcm hcLeaf hd3 hdm hdLeaf).mpr
      (hV2 s a b c d hSourceSplit hab hcd
        haLeaf hbLeaf hcLeaf hdLeaf hSourceAB hSourceCD)

end DiaryLeafPriority
end ThreeUniformDiaries
