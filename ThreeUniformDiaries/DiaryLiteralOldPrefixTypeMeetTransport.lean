import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface
import ThreeUniformDiaries.ExactTypeMeetLevels

/-!
# Track B: literal finite initial-segment agreement preserves EXACT
# singleton types, numerical singleton meets and marker-defined roles

This is a necessary missing interface for the no-literal-full-diary
end-extension adversarial audit. The two graphs may have arbitrary
different edges beyond a finite cut n; only the REAL old third
coordinate c<n is compared. Finite zero-extended source diagrams
are not incorrectly promoted to global RoleDiary structures.

The type tests (x,y,u) have old third coordinate u<n; hence they
agree at ALL cuts, and their capped greatest agreement levels
are LITERALLY equal. The same old marker triples give exactly the
three role equivalences.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A C : Ordered3Graph Nat} {n : Nat}

/-- An old edge diagram is identical to the corresponding old
initial segment of a potentially much larger target diagram.
No assumption on either graph's Nat tail is required. -/
def LiteralOldPrefixAgreement
    (A C : Ordered3Graph Nat) (n : Nat) : Prop :=
  ∀ a b c : Nat, c < n → (A.edge a b c ↔ C.edge a b c)

/-- Singleton types of two old vertices are literally the same in
the source and target at EVERY numerical type cut, not only at
cuts below n. Every last coordinate in those tests is old. -/
theorem sameOneTypeBelow_iff_of_literalOldPrefix
    (h : LiteralOldPrefixAgreement A C n)
    (u v l : Nat) (hu : u < n) (hv : v < n) :
    A.SameOneTypeBelow l u v ↔ C.SameOneTypeBelow l u v := by
  constructor
  · intro hA a b hab hbl
    have hU := h a b u hu
    have hV := h a b v hv
    exact hU.symm.trans ((hA hab hbl).trans hV)
  · intro hC a b hab hbl
    have hU := h a b u hu
    have hV := h a b v hv
    exact hU.trans ((hC hab hbl).trans hV.symm)

/-- Exact old singleton meets are invariant under any later
completion modifying only the part of the edge table with last
coordinate at least n. This holds for mixed source roles too. -/
theorem oneMeetLevel_eq_of_literalOldPrefix
    (h : LiteralOldPrefixAgreement A C n)
    (u v : Nat) (hu : u < n) (hv : v < n) :
    A.oneMeetLevel u v = C.oneMeetLevel u v := by
  classical
  have hTypes (l : Nat) :
      A.SameOneTypeBelow l u v ↔ C.SameOneTypeBelow l u v :=
    sameOneTypeBelow_iff_of_literalOldPrefix h u v l hu hv
  apply le_antisymm
  · have hAgree : C.SameOneTypeBelow (A.oneMeetLevel u v) u v :=
      (hTypes _).mp (A.oneMeetLevel_agree u v)
    exact Nat.le_findGreatest
      (A.oneMeetLevel_le_min u v) hAgree
  · have hAgree : A.SameOneTypeBelow (C.oneMeetLevel u v) u v :=
      (hTypes _).mpr (C.oneMeetLevel_agree u v)
    exact Nat.le_findGreatest
      (C.oneMeetLevel_le_min u v) hAgree

/-- All old marker-coded roles (leaf, one-split, two-split)
reflect both ways, not just the positive edge incidence. -/
theorem role_iff_of_literalOldPrefix
    (h : LiteralOldPrefixAgreement A C n)
    (u : Nat) (hu : u < n) :
    (IsLeaf A u ↔ IsLeaf C u) ∧
    (IsOneSplit A u ↔ IsOneSplit C u) ∧
    (IsTwoSplit A u ↔ IsTwoSplit C u) := by
  have h01 : A.edge 0 1 u ↔ C.edge 0 1 u := h 0 1 u hu
  have h02 : A.edge 0 2 u ↔ C.edge 0 2 u := h 0 2 u hu
  constructor
  · simp only [IsLeaf]
    simp [h01,h02]
  constructor
  · simp only [IsOneSplit]
    simp [h01,h02]
  · simp only [IsTwoSplit]
    simp [h01,h02]

end DiaryLeafPriority
end ThreeUniformDiaries
