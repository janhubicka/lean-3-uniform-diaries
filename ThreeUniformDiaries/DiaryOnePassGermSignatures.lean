import ThreeUniformDiaries.DiaryOnePassCodeEquivalence
import ThreeUniformDiaries.DiaryOnePassStaticCodeTransport

/-!
# The actual finite parent-and-germ signatures for one-pass blocks

For original cut m, singleton and full pair parents are the exact
finite oneCode/twoCode spaces. A NORMAL child is labelled by its
next-cut type, and the TERMINAL child is labelled separately by none.
A terminal pair child occurs when the first pair member is m.

This is the real source-dependent finite signature interface needed
to select a finite list of event classes at each original cut. Unlike
the synthetic one-hot lemma, it uses the manuscript's actual singleton
and full two-type definitions. It makes no assertion about the final
target hypergraph, V/E/S, or flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A singleton parent code at m with either a successor normal
child code or a distinguished terminal child. -/
abbrev OneGermSpace (m : Nat) : Type :=
  OneCodeSpace m × Option (OneCodeSpace (m + 1))

/-- A full pair parent code at m with either a successor normal
child code or a distinguished terminal pair child. -/
abbrev TwoGermSpace (m : Nat) : Type :=
  TwoCodeSpace m × Option (TwoCodeSpace (m + 1))

noncomputable def oneGermCode
    (H : Ordered3Graph Nat) (m u : Nat) : OneGermSpace m :=
  (oneCode H m u,
    if u = m then none else some (oneCode H (m + 1) u))

noncomputable def twoGermCode
    (H : Ordered3Graph Nat) (m u v : Nat) : TwoGermSpace m :=
  (twoCode H m u v,
    if u = m then none else some (twoCode H (m + 1) u v))

/-- The germ alphabet is finite even for countable sources. -/
theorem finite_oneGermSpace (m : Nat) :
    Finite (OneGermSpace m) := by
  infer_instance

theorem finite_twoGermSpace (m : Nat) :
    Finite (TwoGermSpace m) := by
  infer_instance

/-- There can be only finitely many realised singleton germs
at any fixed old cut (without any finiteness of the source). -/
theorem finite_realised_oneGerms
    (H : Ordered3Graph Nat) (m : Nat) :
    Finite {g : OneGermSpace m // ∃ u : Nat, oneGermCode H m u = g} := by
  infer_instance

/-- Likewise for the realised full ordered-pair germs. -/
theorem finite_realised_twoGerms
    (H : Ordered3Graph Nat) (m : Nat) :
    Finite {g : TwoGermSpace m // ∃ u v : Nat,
      twoGermCode H m u v = g} := by
  infer_instance

/-- Two normal singleton germs are identical iff BOTH their old
parent type and their next-cut singleton child type agree. -/
theorem oneGerm_eq_iff_normal
    (H : Ordered3Graph Nat) (m u v : Nat)
    (hu : u ≠ m) (hv : v ≠ m) :
    oneGermCode H m u = oneGermCode H m v ↔
      H.SameOneTypeBelow m u v ∧
      H.SameOneTypeBelow (m + 1) u v := by
  simp [oneGermCode, hu, hv, oneCode_eq_iff_sameOneType]

/-- The terminal singleton child is disjoint from every normal
child, independently of the parent code. -/
theorem oneGerm_terminal_ne_normal
    (H : Ordered3Graph Nat) (m u : Nat) (hu : u ≠ m) :
    oneGermCode H m m ≠ oneGermCode H m u := by
  intro h
  have hchild := congrArg Prod.snd h
  simp [oneGermCode, hu] at hchild

/-- Two normal pair germs are identical iff BOTH their old
full pair parent and their next full pair child types agree. -/
theorem twoGerm_eq_iff_normal
    (H : Ordered3Graph Nat) (m a b c d : Nat)
    (ha : a ≠ m) (hc : c ≠ m) :
    twoGermCode H m a b = twoGermCode H m c d ↔
      H.SameTwoTypeBelow m a b c d ∧
      H.SameTwoTypeBelow (m + 1) a b c d := by
  simp [twoGermCode, ha, hc, twoCode_eq_iff_sameTwoType]

/-- Terminal pair germs at the same original cut have the
same combined germ signature exactly when they have the same
original full parent type: there is only ONE terminal child
in each full pair parent fibre. -/
theorem twoGerm_terminal_eq_iff_parent
    (H : Ordered3Graph Nat) (m u v : Nat) :
    twoGermCode H m m u = twoGermCode H m m v ↔
      H.SameTwoTypeBelow m m u m v := by
  simp [twoGermCode, twoCode_eq_iff_sameTwoType]

/-- A terminal pair germ and a normal pair germ cannot be
identified, even when their original full parent types agree. -/
theorem twoGerm_terminal_ne_normal
    (H : Ordered3Graph Nat) (m u a b : Nat) (ha : a ≠ m) :
    twoGermCode H m m u ≠ twoGermCode H m a b := by
  intro h
  have hchild := congrArg Prod.snd h
  simp [twoGermCode, ha] at hchild

/-- In one terminal pair parent, the later leaf's NEXT
singleton code is fixed. This is the nontrivial capped
pair-germ compatibility needed for delayed singleton tests. -/
theorem terminal_twoGerm_forces_next_oneCode
    (H : Ordered3Graph Nat) (m u v : Nat)
    (h : twoGermCode H m m u = twoGermCode H m m v) :
    oneCode H (m + 1) u = oneCode H (m + 1) v := by
  apply (terminalTwoCode_eq_iff_nextOneCode H m u v).mp
  exact congrArg Prod.fst h

end DiaryLeafPriority
end ThreeUniformDiaries
