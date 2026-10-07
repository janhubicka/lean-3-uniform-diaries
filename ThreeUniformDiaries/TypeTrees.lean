import Mathlib

/-!
# The three concrete type trees

This is the finite data underlying the vector tree in the repaired
aux-type Ramsey proof.

A level-`n` enumeration node stores ternary edge bits whose largest
coordinate is below `n`.  A 1-type node stores pair bits below `n`,
and an auxiliary-type node stores single bits below `n`.

Using finite-support functions on `Nat` keeps the successor operations
literal: one new level appends exactly the bits described in the manuscript.
-/

namespace ThreeUniformDiaries

/-- Auxiliary types on level `n`. -/
structure AuxNode (n : Nat) where
  bit : Nat → Bool
  support : ∀ i, n ≤ i → bit i = false

/-- 1-types on level `n`.  Only the second coordinate controls support;
the intended use is on increasing pairs. -/
structure OneNode (n : Nat) where
  pair : Nat → Nat → Bool
  support : ∀ i j, n ≤ j → pair i j = false

/-- Enumerated 3-hypergraphs on level `n`.  Only the largest coordinate
controls support; the intended use is on increasing triples. -/
structure EnumNode (n : Nat) where
  triple : Nat → Nat → Nat → Bool
  support : ∀ i j k, n ≤ k → triple i j k = false

namespace AuxNode

/-- Add the level-`n` auxiliary bit. -/
def succ {n : Nat} (a : AuxNode n) (e : Bool) : AuxNode (n + 1) where
  bit i := if i = n then e else a.bit i
  support := by
    intro i hi
    have hne : i ≠ n := by omega
    rw [if_neg hne]
    exact a.support i (by omega)

@[simp] theorem succ_new {n : Nat} (a : AuxNode n) (e : Bool) :
    (a.succ e).bit n = e := by
  simp [succ]

theorem succ_old {n : Nat} (a : AuxNode n) (e : Bool)
    {i : Nat} (hi : i < n) :
    (a.succ e).bit i = a.bit i := by
  have hne : i ≠ n := by omega
  simp [succ, hne]

end AuxNode

namespace OneNode

/-- Add level `n` to a 1-type.  The new pair bits are read from the
level-`n` auxiliary type. -/
def succ {n : Nat} (b : OneNode n) (c : AuxNode n) : OneNode (n + 1) where
  pair i j := if j = n then c.bit i else b.pair i j
  support := by
    intro i j hj
    have hne : j ≠ n := by omega
    rw [if_neg hne]
    exact b.support i j (by omega)

@[simp] theorem succ_new {n : Nat} (b : OneNode n) (c : AuxNode n)
    (i : Nat) :
    (b.succ c).pair i n = c.bit i := by
  simp [succ]

theorem succ_old {n : Nat} (b : OneNode n) (c : AuxNode n)
    {i j : Nat} (hj : j < n) :
    (b.succ c).pair i j = b.pair i j := by
  have hne : j ≠ n := by omega
  simp [succ, hne]

end OneNode

namespace EnumNode

/-- Add level `n` to an enumeration.  The new triples are read from the
level-`n` 1-type. -/
def succ {n : Nat} (a : EnumNode n) (b : OneNode n) : EnumNode (n + 1) where
  triple i j k := if k = n then b.pair i j else a.triple i j k
  support := by
    intro i j k hk
    have hne : k ≠ n := by omega
    rw [if_neg hne]
    exact a.support i j k (by omega)

@[simp] theorem succ_new {n : Nat} (a : EnumNode n) (b : OneNode n)
    (i j : Nat) :
    (a.succ b).triple i j n = b.pair i j := by
  simp [succ]

theorem succ_old {n : Nat} (a : EnumNode n) (b : OneNode n)
    {i j k : Nat} (hk : k < n) :
    (a.succ b).triple i j k = a.triple i j k := by
  have hne : k ≠ n := by omega
  simp [succ, hne]

/-- Truncate an enumeration at a cut `l`. -/
def truncate {N : Nat} (H : EnumNode N) (l : Nat) : EnumNode l where
  triple i j k := if k < l then H.triple i j k else false
  support := by
    intro i j k hk
    rw [if_neg (Nat.not_lt.mpr hk)]

/-- The 1-type of `v` over the cut `l`. -/
def oneType {N : Nat} (H : EnumNode N) (l v : Nat) : OneNode l where
  pair i j := if j < l then H.triple i j v else false
  support := by
    intro i j hj
    rw [if_neg (Nat.not_lt.mpr hj)]

/-- The auxiliary type of the ordered pair `u,v` over the cut `l`. -/
def auxType {N : Nat} (H : EnumNode N) (l u v : Nat) : AuxNode l where
  bit i := if i < l then H.triple i u v else false
  support := by
    intro i hi
    rw [if_neg (Nat.not_lt.mpr hi)]

theorem auxType_succ_bit {N l u v i : Nat} (H : EnumNode N) :
    (H.auxType (l + 1) u v).bit i =
      ((H.auxType l u v).succ (H.triple l u v)).bit i := by
  by_cases hil : i < l
  · have hine : i ≠ l := by omega
    simp [auxType, AuxNode.succ, hil, hine, show i < l + 1 by omega]
  · by_cases hieq : i = l
    · subst i
      simp [auxType, AuxNode.succ]
    · have hge : l + 1 ≤ i := by omega
      have hnlt : ¬ i < l := by omega
      have hnlt' : ¬ i < l + 1 := by omega
      simp [auxType, AuxNode.succ, hieq, hnlt, hnlt']

theorem oneType_succ_pair {N l v i j : Nat} (H : EnumNode N) :
    (H.oneType (l + 1) v).pair i j =
      ((H.oneType l v).succ (H.auxType l l v)).pair i j := by
  by_cases hjl : j < l
  · have hjne : j ≠ l := by omega
    simp [oneType, auxType, OneNode.succ, hjl, hjne,
      show j < l + 1 by omega]
  · by_cases hjeq : j = l
    · subst j
      simp [oneType, auxType, OneNode.succ]
  · have hge : l + 1 ≤ j := by omega
    have hnlt : ¬ j < l := by omega
    have hnlt' : ¬ j < l + 1 := by omega
    have hjne : j ≠ l := by omega
    simp [oneType, auxType, OneNode.succ, hnlt, hnlt', hjne]

theorem truncate_succ_triple {N l i j k : Nat} (H : EnumNode N) :
    (H.truncate (l + 1)).triple i j k =
      ((H.truncate l).succ (H.oneType l l)).triple i j k := by
  by_cases hkl : k < l
  · have hkne : k ≠ l := by omega
    simp [truncate, oneType, succ, hkl, hkne,
      show k < l + 1 by omega]
  · by_cases hkeq : k = l
    · subst k
      simp [truncate, oneType, succ]
    · have hge : l + 1 ≤ k := by omega
      have hnlt : ¬ k < l := by omega
      have hnlt' : ¬ k < l + 1 := by omega
      have hkne : k ≠ l := by omega
      simp [truncate, oneType, succ, hnlt, hnlt', hkne]

end EnumNode

end ThreeUniformDiaries
