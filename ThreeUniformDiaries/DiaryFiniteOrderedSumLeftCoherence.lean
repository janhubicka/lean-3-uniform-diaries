import ThreeUniformDiaries.DiaryFiniteOrderedSumLeftTypeTransport
import ThreeUniformDiaries.DiaryFiniteOrderedSumRoles

/-!
# V1/V2 coherence at original left splits in finite ordered sums

Every positive incidence at an original left 1-split or 2-split
comes entirely from the induced left block. This is more than
the internal induced-edge equivalence: we prove the right block
and cross Devlin edges cannot add any new positive leaf or pair
at a left split.

The source left V1/V2 positive classes therefore carry over
using exact left singleton/full-pair prefix type transport.
No source/target global pre-diary, witness or S1/S2 axiom is
postulated. The cross orientation bits remain arbitrary.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- A positive target incidence with marker zero and a genuine
left nonmarker middle vertex ends in the left block. -/
theorem finiteTwoBlockCarrier_left_oneSplit_positive_is_source
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (s a : Nat) (hs3 : 3 ≤ s) (hsn : s < n)
    (hPos : (finiteTwoBlockCarrier H K n m bits).edge 0 s a) :
    a < n ∧ H.edge 0 s a := by
  rcases hPos with hLeft | hRight | hCross
  · exact ⟨hLeft.2, hLeft.1⟩
  · obtain ⟨a', b', c', _hK, _hcm, _hx, hs, _ha⟩ := hRight
    by_cases hbSmall : b' < 3
    · rw [rightBlockImage_marker n b' hbSmall] at hs
      omega
    · have hbRight : n ≤ rightBlockImage n b' :=
        rightBlockImage_nonmarker_ge n b'
          FH.length_ge_three (by omega)
      omega
  · obtain ⟨u,v,_hu3,_hun,_huLeaf,_hv3,_hvm,_hvLeaf,
       _hy,_hz,hBit⟩ := hCross
    rcases hBit with hOne | hTwo
    · omega
    · omega

/-- At a left nonmarker first coordinate, every positive ordered
pair incidence is internal to the original left block. -/
theorem finiteTwoBlockCarrier_left_twoSplit_positive_is_source
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (s a b : Nat) (hs3 : 3 ≤ s) (hsn : s < n)
    (hPos : (finiteTwoBlockCarrier H K n m bits).edge s a b) :
    b < n ∧ H.edge s a b := by
  rcases hPos with hLeft | hRight | hCross
  · exact ⟨hLeft.2, hLeft.1⟩
  · obtain ⟨a', b', c', _hK, _hcm, hs, _hy, _hz⟩ := hRight
    by_cases haSmall : a' < 3
    · rw [rightBlockImage_marker n a' haSmall] at hs
      omega
    · have haRight : n ≤ rightBlockImage n a' :=
        rightBlockImage_nonmarker_ge n a'
          FH.length_ge_three (by omega)
      omega
  · obtain ⟨u,v,_hu3,_hun,_huLeaf,_hv3,_hvm,_hvLeaf,
       _hy,_hz,hBit⟩ := hCross
    rcases hBit with hOne | hTwo
    · omega
    · omega

/-- The actual V1 coherence clause at any left-block one-split.
The source coherence assumption is only about its finite table. -/
theorem finiteTwoBlockCarrier_left_oneSplit_coherent
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hV1 : ∀ s a b : Nat,
      IsOneSplit H s → IsLeaf H a → IsLeaf H b →
      H.edge 0 s a → H.edge 0 s b →
      H.SameOneTypeBelow s a b)
    (bits : Nat → Bool)
    (s a b : Nat) (hs3 : 3 ≤ s) (hsn : s < n)
    (hSplit : IsOneSplit (finiteTwoBlockCarrier H K n m bits) s)
    (haLeaf : IsLeaf (finiteTwoBlockCarrier H K n m bits) a)
    (hbLeaf : IsLeaf (finiteTwoBlockCarrier H K n m bits) b)
    (haPos : (finiteTwoBlockCarrier H K n m bits).edge 0 s a)
    (hbPos : (finiteTwoBlockCarrier H K n m bits).edge 0 s b) :
    (finiteTwoBlockCarrier H K n m bits).SameOneTypeBelow s a b := by
  obtain ⟨han,haSource⟩ :=
    finiteTwoBlockCarrier_left_oneSplit_positive_is_source
      FH FK bits s a hs3 hsn haPos
  obtain ⟨hbn,hbSource⟩ :=
    finiteTwoBlockCarrier_left_oneSplit_positive_is_source
      FH FK bits s b hs3 hsn hbPos
  have hsSource : IsOneSplit H s :=
    (finiteTwoBlockCarrier_left_oneSplit_iff
      FH FK bits s hsn).mp hSplit
  have haSourceLeaf : IsLeaf H a :=
    (finiteTwoBlockCarrier_left_leaf_iff
      FH FK bits a han).mp haLeaf
  have hbSourceLeaf : IsLeaf H b :=
    (finiteTwoBlockCarrier_left_leaf_iff
      FH FK bits b hbn).mp hbLeaf
  exact (finiteTwoBlockCarrier_left_oneType_iff
    FH FK bits s a b han hbn).mpr
      (hV1 s a b hsSource haSourceLeaf hbSourceLeaf haSource hbSource)

/-- The actual V2 coherence clause at any left-block two-split.
Positive target pairs are shown to be internal BEFORE using the
source coherence and transported full type equality. -/
theorem finiteTwoBlockCarrier_left_twoSplit_coherent
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hV2 : ∀ s a b c d : Nat,
      IsTwoSplit H s → a < b → c < d →
      IsLeaf H a → IsLeaf H b → IsLeaf H c → IsLeaf H d →
      H.edge s a b → H.edge s c d →
      H.SameTwoTypeBelow s a b c d)
    (bits : Nat → Bool)
    (s a b c d : Nat) (hs3 : 3 ≤ s) (hsn : s < n)
    (hab : a < b) (hcd : c < d)
    (hSplit : IsTwoSplit (finiteTwoBlockCarrier H K n m bits) s)
    (haLeaf : IsLeaf (finiteTwoBlockCarrier H K n m bits) a)
    (hbLeaf : IsLeaf (finiteTwoBlockCarrier H K n m bits) b)
    (hcLeaf : IsLeaf (finiteTwoBlockCarrier H K n m bits) c)
    (hdLeaf : IsLeaf (finiteTwoBlockCarrier H K n m bits) d)
    (hAB : (finiteTwoBlockCarrier H K n m bits).edge s a b)
    (hCD : (finiteTwoBlockCarrier H K n m bits).edge s c d) :
    (finiteTwoBlockCarrier H K n m bits).SameTwoTypeBelow
      s a b c d := by
  obtain ⟨hbn,hSourceAB⟩ :=
    finiteTwoBlockCarrier_left_twoSplit_positive_is_source
      FH FK bits s a b hs3 hsn hAB
  obtain ⟨hdn,hSourceCD⟩ :=
    finiteTwoBlockCarrier_left_twoSplit_positive_is_source
      FH FK bits s c d hs3 hsn hCD
  have han : a < n := by omega
  have hcn : c < n := by omega
  have hsSource : IsTwoSplit H s :=
    (finiteTwoBlockCarrier_left_twoSplit_iff
      FH FK bits s hsn).mp hSplit
  have haSourceLeaf : IsLeaf H a :=
    (finiteTwoBlockCarrier_left_leaf_iff FH FK bits a han).mp haLeaf
  have hbSourceLeaf : IsLeaf H b :=
    (finiteTwoBlockCarrier_left_leaf_iff FH FK bits b hbn).mp hbLeaf
  have hcSourceLeaf : IsLeaf H c :=
    (finiteTwoBlockCarrier_left_leaf_iff FH FK bits c hcn).mp hcLeaf
  have hdSourceLeaf : IsLeaf H d :=
    (finiteTwoBlockCarrier_left_leaf_iff FH FK bits d hdn).mp hdLeaf
  exact (finiteTwoBlockCarrier_left_twoType_iff
    FH FK bits s a b c d han hbn hcn hdn).mpr
      (hV2 s a b c d hsSource hab hcd
        haSourceLeaf hbSourceLeaf hcSourceLeaf hdSourceLeaf
        hSourceAB hSourceCD)

end DiaryLeafPriority
end ThreeUniformDiaries
