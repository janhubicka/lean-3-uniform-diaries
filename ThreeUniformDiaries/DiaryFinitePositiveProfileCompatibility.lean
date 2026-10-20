import ThreeUniformDiaries.DiaryFlipPositiveTypeCodes
import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface

/-!
# Necessary positive-profile compatibility in FINITE pre-diaries

The original diary flip-prefix amalgam erroneously identifies
early split vertices on the basis of chronological flip prefixes.
This is refuted by genuine nine-vertex flips: two positive
ordered leaf pairs may have incompatible marker-one auxiliary
bits at a shared two-split.

This module exports the obstruction and the stronger positive
type-code invariant in the actual bounded finite pre-diary API.
It is a STRICTLY NECESSARY condition, not a construction of a
common flip tree or a proof of every-flip absorption.

A possible later construction may share 1-splits/2-splits only
when these entire positive codes agree; even then V3 relations
with third-party earlier leaves must still be reconciled.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat} {n : Nat}

/-- For any finite pre-diary, all positively incident leaves
at a retained 1-split have identical full singleton codes
below that split, including early Devlin marker tests. -/
theorem FiniteRolePrediaryBlock.oneSplit_positive_code_unique
    (P : FiniteRolePrediaryBlock H n)
    (m a b : Nat) (hm : IsOneSplit H m)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hPosA : H.edge 0 m a) (hPosB : H.edge 0 m b) :
    oneCode H m a = oneCode H m b := by
  exact oneCode_eq_of_sameType H m a b
    (P.one_split_coherent m a b hm ha hb hPosA hPosB)

/-- For any finite pre-diary, all positively incident ordered
leaf pairs at a 2-split have IDENTICAL full ordered-pair
types below that split (both singleton coordinates and the
auxiliary coordinate), not just equal early marker bits. -/
theorem FiniteRolePrediaryBlock.twoSplit_positive_code_unique
    (P : FiniteRolePrediaryBlock H n)
    (m a b c d : Nat) (hm : IsTwoSplit H m)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hPosAB : H.edge m a b) (hPosCD : H.edge m c d) :
    twoCode H m a b = twoCode H m c d := by
  exact twoCode_eq_of_sameType H m a b c d
    (P.two_split_coherent m a b c d hm hab hcd
      ha hb hc hd hPosAB hPosCD)

/-- In particular, opposite marker-one bits on positive
leaf pairs are impossible at one and the same target 2-split.
This is the obstruction witnessed by the published
nine-vertex flips at their chronological shared root. -/
theorem FiniteRolePrediaryBlock.twoSplit_positive_marker_one_agrees
    (P : FiniteRolePrediaryBlock H n)
    (m a b c d : Nat) (hm : IsTwoSplit H m)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hPosAB : H.edge m a b) (hPosCD : H.edge m c d) :
    H.edge 1 a b ↔ H.edge 1 c d := by
  have hSame := P.two_split_coherent
    m a b c d hm hab hcd ha hb hc hd hPosAB hPosCD
  have h1m : 1 < m := by omega
  exact hSame.2.2 h1m

end DiaryLeafPriority
end ThreeUniformDiaries
