import ThreeUniformDiaries.DiaryFinitePositiveTwoSplitAnchor
import ThreeUniformDiaries.DiaryFinitePositiveAnchorEquivalence
import ThreeUniformDiaries.DiaryFlipPositiveTypeCodes

/-!
# At a genuine S2 split, every positive pair has the same parent code

Let s be a genuine two-split with two fixed ordered leaf-pair
witnesses W=(a,b), W'=(c,d) meeting at s in FULL two-type.
Their complete predecessor pair-type codes below s are equal,
because their full pair meet is s.

The first-disagreement E3 rule gives opposite E3 bits at s
for W,W'. Thus in any finite diary one of W,W' is positive.
V2 coherence forces EVERY positive pair at s to agree below
s with that positive witness, and therefore with BOTH
witnesses' common parent code.

Consequently the complete positive full 2-type profile at s
is determined by the underlying S2 witness meet, NOT by the
choice of the positive successor orientation at s. This is a
source-side compatibility lemma for future sign-rooted
shared-split amalgamation. It does not assign cross-branch
Devlin edges or prove any every-target-flip absorber.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The complete predecessor pair-type code at a genuine
two-split is the same for every positively incident pair,
and agrees with a FIXED S2 witness pair, whether that
particular witness is positive or negative at the split.

The witness pair W' is needed only to show the first pair
W and W' are opposite at s; both have the same pair type
strictly below s by their full meet. -/
theorem finite_positive_twoSplit_parent_code_eq_witness
    {H : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRoleDiaryBlock H n)
    (s a b c d u v : Nat)
    (hs : IsTwoSplit H s)
    (hab : a < b) (hcd : c < d) (huv : u < v)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hsa : s < a) (hsc : s < c)
    (hMeet : H.twoMeetLevel a b c d = s)
    (hPositive : H.edge s u v) :
    twoCode H s u v = twoCode H s a b := by
  have hWitnessBelow : H.SameTwoTypeBelow s a b c d := by
    rw [← hMeet]
    exact H.twoMeetLevel_agree a b c d
  have hWitnessCode :
      twoCode H s a b = twoCode H s c d :=
    twoCode_eq_of_sameType H s a b c d hWitnessBelow
  by_cases hPosFirst : H.edge s a b
  · have hSame : H.SameTwoTypeBelow s u v a b :=
      D.prediary.two_split_coherent
        s u v a b hs huv hab hu hv ha hb hPositive hPosFirst
    exact twoCode_eq_of_sameType H s u v a b hSame
  · have hOpp : ¬ (H.edge s a b ↔ H.edge s c d) :=
      E_twoSplit_pair_aux_distinguishes
        D.prediary.permitted_edge s a b c d hs hsa hsc hMeet
    have hPosSecond : H.edge s c d := by
      by_contra hNeg
      exact hOpp (iff_of_false hPosFirst hNeg)
    have hSame : H.SameTwoTypeBelow s u v c d :=
      D.prediary.two_split_coherent
        s u v c d hs huv hcd hu hv hc hd hPositive hPosSecond
    exact (twoCode_eq_of_sameType H s u v c d hSame).trans
      hWitnessCode.symm

/-- A designated S2 witness pair represents a UNIQUE full
parent type code for the whole positive E3 class, so flipping
the positive side at this split does not choose a different
predecessor type. No E3 independence across distinct splits
is assumed or asserted. -/
theorem finite_twoSplit_positive_parent_profile_unique
    {H : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRoleDiaryBlock H n)
    (s a b c d u v x y : Nat)
    (hs : IsTwoSplit H s)
    (hab : a < b) (hcd : c < d)
    (huv : u < v) (hxy : x < y)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hx : IsLeaf H x) (hy : IsLeaf H y)
    (hsa : s < a) (hsc : s < c)
    (hMeet : H.twoMeetLevel a b c d = s)
    (hPosUV : H.edge s u v)
    (hPosXY : H.edge s x y) :
    twoCode H s u v = twoCode H s x y := by
  have hU :=
    finite_positive_twoSplit_parent_code_eq_witness
      D s a b c d u v hs hab hcd huv
      ha hb hc hd hu hv hsa hsc hMeet hPosUV
  have hX :=
    finite_positive_twoSplit_parent_code_eq_witness
      D s a b c d x y hs hab hcd hxy
      ha hb hc hd hx hy hsa hsc hMeet hPosXY
  exact hU.trans hX.symm

end DiaryLeafPriority
end ThreeUniformDiaries
