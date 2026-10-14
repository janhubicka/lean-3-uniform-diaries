import ThreeUniformDiaries.DiaryPointedShapeTransport

/-!
# Leaf-pair 2-types decide the two-tail versus three-tail envelope case

Equality of the *full* 2-type of two ordered pairs below a cut
implies equivalence of their internal singleton-type agreements
below that cut. For pairs whose vertices lie above the cut, this is
equivalent to their singleton meet occurring on the same side of
the protected prefix. No diary-specific axiom is needed here.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Equal ordinary 2-types force the same internal agreement of
the two singleton types within each pair. -/
theorem sameTwoTypeBelow_internal_one_iff
    (H : Ordered3Graph Nat) (i a b c d : Nat)
    (hpair : H.SameTwoTypeBelow i a b c d) :
    H.SameOneTypeBelow i a b ↔ H.SameOneTypeBelow i c d := by
  obtain ⟨hA, hB, _⟩ := hpair
  constructor
  · intro hab x y hxy hy
    calc
      H.edge x y c ↔ H.edge x y a := (hA hxy hy).symm
      _ ↔ H.edge x y b := hab hxy hy
      _ ↔ H.edge x y d := hB hxy hy
  · intro hcd x y hxy hy
    calc
      H.edge x y a ↔ H.edge x y c := hA hxy hy
      _ ↔ H.edge x y d := hcd hxy hy
      _ ↔ H.edge x y b := (hB hxy hy).symm

/-- Internal singleton-type agreement through the cut is equivalent
to the exact capped singleton meet being at or after that cut. -/
theorem oneMeetLevel_ge_iff_sameOneTypeBelow
    (H : Ordered3Graph Nat) (i a b : Nat)
    (hia : i ≤ a) (hib : i ≤ b) :
    i ≤ H.oneMeetLevel a b ↔ H.SameOneTypeBelow i a b := by
  classical
  constructor
  · intro hmeet x y hxy hy
    exact (H.oneMeetLevel_agree a b) hxy (lt_of_lt_of_le hy hmeet)
  · intro hsame
    exact Nat.le_findGreatest (le_min hia hib) hsame

/-- Same-type leaf pairs select the same envelope case: either
both singleton meets lie below the cut (two tails), or both lie
at/after it (three tails). -/
theorem sameTwoTypeBelow_same_envelope_case
    (H : Ordered3Graph Nat) (i a b c d : Nat)
    (hia : i ≤ a) (hib : i ≤ b)
    (hic : i ≤ c) (hid : i ≤ d)
    (hpair : H.SameTwoTypeBelow i a b c d) :
    (H.oneMeetLevel a b < i ↔ H.oneMeetLevel c d < i) := by
  have hAB : i ≤ H.oneMeetLevel a b ↔
      H.SameOneTypeBelow i a b :=
    H.oneMeetLevel_ge_iff_sameOneTypeBelow i a b hia hib
  have hCD : i ≤ H.oneMeetLevel c d ↔
      H.SameOneTypeBelow i c d :=
    H.oneMeetLevel_ge_iff_sameOneTypeBelow i c d hic hid
  have hside : (i ≤ H.oneMeetLevel a b) ↔
      (i ≤ H.oneMeetLevel c d) :=
    hAB.trans ((H.sameTwoTypeBelow_internal_one_iff i a b c d hpair).trans
      hCD.symm)
  constructor
  · intro hsmall
    by_contra hnot
    have hlargeCD : i ≤ H.oneMeetLevel c d := by omega
    have hlargeAB := hside.mpr hlargeCD
    omega
  · intro hsmall
    by_contra hnot
    have hlargeAB : i ≤ H.oneMeetLevel a b := by omega
    have hlargeCD := hside.mp hlargeAB
    omega

end Ordered3Graph
end ThreeUniformDiaries
