import ThreeUniformDiaries.DiaryFiniteDummyTailCarrier
import ThreeUniformDiaries.DiaryOnePassGermSignatures
import Lean.Elab.Tactic.Omega

/-!
# Track B: dummy-tail leaves and pairs have one old-cut germ profile

The verified finiteDummyTailCarrier keeps a genuine finite pre-diary
on [0,n) and adds infinitely many genuine leaves at positions >=n.
The cross marker bits depend on the OLD middle leaf coordinate, not
on the chosen new last leaf. No edges with first nonmarker coordinate
touch the tail, and on ordered pairs of new tail leaves the only
positive edge has marker 1 as its first coordinate.

Consequently ALL tail leaves have literally the same singleton type
below every old cut m<=n, and ALL ordered pairs of tail leaves have
literally the same FULL ordered-pair type below those cuts, including
the auxiliary coordinate and the two singleton coordinates.

Even at the next-cut level m+1<=n this remains true. Hence all
pure-tail one-germ codes and all pure-tail pair-germ codes at any
old m<n are identical. This is a POSITIVE reduction of the remaining
relative protected-prefix construction: genuine germ competition at
an old cut cannot come from two pure tail children; only old-vs-tail
or other non-tail source classes can create new selected events.

This is a concrete relational fact about the actual carrier, NOT a
proof that its V/E/S prediary orientations can be selected with no
old-prefix events, and NOT relative finite absorber existence.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- All edges whose LAST vertex lies in the dummy tail and
whose MIDDLE coordinate is old have exactly the same cross
marker-bit formula, regardless of which tail leaf is chosen. -/
theorem finiteDummyTail_oldMiddle_tailEdge_iff
    (H : Ordered3Graph Nat) (n : Nat) (bits : Nat → Bool)
    (x y z : Nat) (hy : y < n) (hz : n ≤ z) :
    (finiteDummyTailCarrier H n bits).edge x y z ↔
      ∃ u : Nat, 3 ≤ u ∧ u < n ∧ IsLeaf H u ∧ y = u ∧
        ((x = 1 ∧ bits u = true) ∨
         (x = 2 ∧ bits u = false)) := by
  constructor
  · intro he
    rcases he with hOld | hCross | hTail
    · omega
    · obtain ⟨u,hu3,hun,hLeaf,_hzn,hEq,hBit⟩ := hCross
      exact ⟨u,hu3,hun,hLeaf,hEq,hBit⟩
    · omega
  · rintro ⟨u,hu3,hun,hLeaf,hEq,hBit⟩
    exact Or.inr (Or.inl ⟨u,hu3,hun,hLeaf,hz,hEq,hBit⟩)

/-- All dummy-tail vertices share the same literal singleton
type at EVERY original cut m<=n, without any assumptions on the
source role structure or V3 bits. -/
theorem finiteDummyTail_allTail_oneTypeBelow_oldCut
    (H : Ordered3Graph Nat) (n : Nat) (bits : Nat → Bool)
    (m u v : Nat) (hm : m ≤ n) (hu : n ≤ u) (hv : n ≤ v) :
    (finiteDummyTailCarrier H n bits).SameOneTypeBelow m u v := by
  intro x y _hxy hym
  have hy : y < n := lt_of_lt_of_le hym hm
  exact (finiteDummyTail_oldMiddle_tailEdge_iff
    H n bits x y u hy hu).trans
      (finiteDummyTail_oldMiddle_tailEdge_iff
        H n bits x y v hy hv).symm

/-- The last two coordinates of any ordered dummy-tail pair
have exactly one marker-one incidence, independently of their
numerical values. There are no other such hyperedges. -/
theorem finiteDummyTail_tailPair_edge_iff_markerOne
    (H : Ordered3Graph Nat) (n : Nat) (bits : Nat → Bool)
    (a b x : Nat) (ha : n ≤ a) (hab : a < b) :
    (finiteDummyTailCarrier H n bits).edge x a b ↔ x = 1 := by
  constructor
  · intro he
    rcases he with hOld | hCross | hTail
    · omega
    · obtain ⟨u,_hu3,hun,_hLeaf,_hzn,hEq,_hBit⟩ := hCross
      omega
    · exact hTail.1
  · intro hx
    exact Or.inr (Or.inr ⟨hx,ha,hab⟩)

/-- Every TWO ordered pairs consisting entirely of dummy-tail
leaves have the same complete full ordered-pair type below any
old cut m<=n, including both coordinate singleton codes and the
auxiliary edge column. -/
theorem finiteDummyTail_allTailPairs_twoTypeBelow_oldCut
    (H : Ordered3Graph Nat) (n : Nat) (bits : Nat → Bool)
    (m a b c d : Nat)
    (hm : m ≤ n)
    (ha : n ≤ a) (hab : a < b)
    (hc : n ≤ c) (hcd : c < d) :
    (finiteDummyTailCarrier H n bits).SameTwoTypeBelow m a b c d := by
  refine ⟨?_,?_,?_⟩
  · exact finiteDummyTail_allTail_oneTypeBelow_oldCut
      H n bits m a c hm ha hc
  · have hb : n ≤ b := by omega
    have hd : n ≤ d := by omega
    exact finiteDummyTail_allTail_oneTypeBelow_oldCut
      H n bits m b d hm hb hd
  · intro x _hx
    exact (finiteDummyTail_tailPair_edge_iff_markerOne
      H n bits a b x ha hab).trans
        (finiteDummyTail_tailPair_edge_iff_markerOne
          H n bits c d x hc hcd).symm

/-- Pure tail leaves have ONE actual singleton germ at every
old m<n, since both their m-parent and (m+1)-child types agree.
No artificial finite-germ approximation is used. -/
theorem finiteDummyTail_allTail_oneGermCode_eq
    (H : Ordered3Graph Nat) (n : Nat) (bits : Nat → Bool)
    (m u v : Nat)
    (hm : m < n) (hu : n ≤ u) (hv : n ≤ v) :
    oneGermCode (finiteDummyTailCarrier H n bits) m u =
      oneGermCode (finiteDummyTailCarrier H n bits) m v := by
  have hmu : u ≠ m := by omega
  have hmv : v ≠ m := by omega
  apply (oneGerm_eq_iff_normal
    (finiteDummyTailCarrier H n bits) m u v hmu hmv).mpr
  constructor
  · exact finiteDummyTail_allTail_oneTypeBelow_oldCut
      H n bits m u v (by omega) hu hv
  · exact finiteDummyTail_allTail_oneTypeBelow_oldCut
      H n bits (m+1) u v (by omega) hu hv

/-- Pure tail ordered pairs have ONE actual full pair-germ
at every old m<n, by equality of BOTH full pair types at
cuts m and m+1. -/
theorem finiteDummyTail_allTail_twoGermCode_eq
    (H : Ordered3Graph Nat) (n : Nat) (bits : Nat → Bool)
    (m a b c d : Nat)
    (hm : m < n)
    (ha : n ≤ a) (hab : a < b)
    (hc : n ≤ c) (hcd : c < d) :
    twoGermCode (finiteDummyTailCarrier H n bits) m a b =
      twoGermCode (finiteDummyTailCarrier H n bits) m c d := by
  have hma : a ≠ m := by omega
  have hmc : c ≠ m := by omega
  apply (twoGerm_eq_iff_normal
    (finiteDummyTailCarrier H n bits)
      m a b c d hma hmc).mpr
  constructor
  · exact finiteDummyTail_allTailPairs_twoTypeBelow_oldCut
      H n bits m a b c d (by omega) ha hab hc hcd
  · exact finiteDummyTail_allTailPairs_twoTypeBelow_oldCut
      H n bits (m+1) a b c d (by omega) ha hab hc hcd

end DiaryLeafPriority
end ThreeUniformDiaries
