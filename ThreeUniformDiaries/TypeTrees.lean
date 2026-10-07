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
  support : ∀ i j, ¬ (i < j ∧ j < n) → pair i j = false

/-- Enumerated 3-hypergraphs on level `n`.  Non-increasing or out-of-level
triples are forced to zero. -/
structure EnumNode (n : Nat) where
  triple : Nat → Nat → Nat → Bool
  support : ∀ i j k, ¬ (i < j ∧ j < k ∧ k < n) → triple i j k = false

@[ext] theorem AuxNode.ext_bits {n : Nat} {a b : AuxNode n}
    (h : a.bit = b.bit) : a = b := by
  cases a
  cases b
  cases h
  rfl

@[ext] theorem OneNode.ext_pairs {n : Nat} {a b : OneNode n}
    (h : a.pair = b.pair) : a = b := by
  cases a
  cases b
  cases h
  rfl

@[ext] theorem EnumNode.ext_triples {n : Nat} {a b : EnumNode n}
    (h : a.triple = b.triple) : a = b := by
  cases a
  cases b
  cases h
  rfl

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
    intro i j hbad
    by_cases hjn : j = n
    · subst j
      rw [if_pos rfl]
      exact c.support i (by omega)
    · rw [if_neg hjn]
      apply b.support i j
      intro hvalid
      exact hbad ⟨hvalid.1, by omega⟩

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
    intro i j k hbad
    by_cases hkn : k = n
    · subst k
      rw [if_pos rfl]
      apply b.support i j
      intro hvalid
      exact hbad ⟨hvalid.1, hvalid.2, by omega⟩
    · rw [if_neg hkn]
      apply a.support i j k
      intro hvalid
      exact hbad ⟨hvalid.1, hvalid.2.1, by omega⟩

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
    intro i j k hbad
    by_cases hkl : k < l
    · rw [if_pos hkl]
      apply H.support i j k
      intro hvalid
      exact hbad ⟨hvalid.1, hvalid.2.1, hkl⟩
    · rw [if_neg hkl]

/-- The 1-type of `v` over the cut `l`. -/
def oneType {N : Nat} (H : EnumNode N) (l v : Nat) : OneNode l where
  pair i j := if j < l then H.triple i j v else false
  support := by
    intro i j hbad
    by_cases hjl : j < l
    · rw [if_pos hjl]
      apply H.support i j v
      intro hvalid
      exact hbad ⟨hvalid.1, hjl⟩
    · rw [if_neg hjl]

/-- The auxiliary type of the ordered pair `u,v` over the cut `l`. -/
def auxType {N : Nat} (H : EnumNode N) (l u v : Nat) : AuxNode l where
  bit i := if i < l then H.triple i u v else false
  support := by
    intro i hi
    rw [if_neg (Nat.not_lt.mpr hi)]

theorem auxType_succ_bit {N l u v i : Nat} (H : EnumNode N) :
    (H.auxType (l + 1) u v).bit i =
      ((H.auxType l u v).succ (H.triple l u v)).bit i := by
  change
    (if i < l + 1 then H.triple i u v else false) =
      (if i = l then H.triple l u v
       else if i < l then H.triple i u v else false)
  by_cases hil : i < l
  · rw [if_pos (by omega), if_neg (by omega), if_pos hil]
  · by_cases hieq : i = l
    · subst i
      simp
    · rw [if_neg (by omega), if_neg hieq, if_neg hil]

theorem oneType_succ_pair {N l v i j : Nat} (H : EnumNode N) :
    (H.oneType (l + 1) v).pair i j =
      ((H.oneType l v).succ (H.auxType l l v)).pair i j := by
  change
    (if j < l + 1 then H.triple i j v else false) =
      (if j = l
       then (if i < l then H.triple i l v else false)
       else if j < l then H.triple i j v else false)
  by_cases hjl : j < l
  · rw [if_pos (by omega), if_neg (by omega), if_pos hjl]
  · by_cases hjeq : j = l
    · subst j
      rw [if_pos (by omega), if_pos rfl]
      by_cases hil : i < l
      · rw [if_pos hil]
      · rw [if_neg hil]
        have hzero : H.triple i l v = false := by
          apply H.support i l v
          intro hvalid
          exact hil hvalid.1
        exact hzero
    · rw [if_neg (by omega), if_neg hjeq, if_neg hjl]

theorem truncate_succ_triple {N l i j k : Nat} (H : EnumNode N) :
    (H.truncate (l + 1)).triple i j k =
      ((H.truncate l).succ (H.oneType l l)).triple i j k := by
  change
    (if k < l + 1 then H.triple i j k else false) =
      (if k = l
       then (if j < l then H.triple i j l else false)
       else if k < l then H.triple i j k else false)
  by_cases hkl : k < l
  · rw [if_pos (by omega), if_neg (by omega), if_pos hkl]
  · by_cases hkeq : k = l
    · subst k
      rw [if_pos (by omega), if_pos rfl]
      by_cases hjl : j < l
      · rw [if_pos hjl]
      · rw [if_neg hjl]
        have hzero : H.triple i j l = false := by
          apply H.support i j l
          intro hvalid
          exact hjl hvalid.2.1
        exact hzero
    · rw [if_neg (by omega), if_neg hkeq, if_neg hkl]

end EnumNode

/-- Each auxiliary-type level is finite. -/
noncomputable instance auxNodeFintype (n : Nat) : Fintype (AuxNode n) := by
  let encode : AuxNode n → (Fin n → Bool) :=
    fun a i => a.bit i
  apply Fintype.ofInjective encode
  intro a b hab
  apply AuxNode.ext_bits
  funext i
  by_cases hi : i < n
  · let ii : Fin n := ⟨i, hi⟩
    exact congrFun hab ii
  · rw [a.support i (Nat.le_of_not_gt hi),
        b.support i (Nat.le_of_not_gt hi)]

/-- Each 1-type level is finite. -/
noncomputable instance oneNodeFintype (n : Nat) : Fintype (OneNode n) := by
  let encode : OneNode n → (Fin n → Fin n → Bool) :=
    fun a i j => a.pair i j
  apply Fintype.ofInjective encode
  intro a b hab
  apply OneNode.ext_pairs
  funext i j
  by_cases hvalid : i < j ∧ j < n
  · have hi : i < n := lt_trans hvalid.1 hvalid.2
    let ii : Fin n := ⟨i, hi⟩
    let jj : Fin n := ⟨j, hvalid.2⟩
    exact congrFun (congrFun hab ii) jj
  · rw [a.support i j hvalid, b.support i j hvalid]

/-- Each enumeration level is finite. -/
noncomputable instance enumNodeFintype (n : Nat) : Fintype (EnumNode n) := by
  let encode : EnumNode n → (Fin n → Fin n → Fin n → Bool) :=
    fun a i j k => a.triple i j k
  apply Fintype.ofInjective encode
  intro a b hab
  apply EnumNode.ext_triples
  funext i j k
  by_cases hvalid : i < j ∧ j < k ∧ k < n
  · have hi : i < n := lt_trans hvalid.1 (lt_trans hvalid.2.1 hvalid.2.2)
    have hj : j < n := lt_trans hvalid.2.1 hvalid.2.2
    let ii : Fin n := ⟨i, hi⟩
    let jj : Fin n := ⟨j, hj⟩
    let kk : Fin n := ⟨k, hvalid.2.2⟩
    exact congrFun (congrFun (congrFun hab ii) jj) kk
  · rw [a.support i j k hvalid, b.support i j k hvalid]

end ThreeUniformDiaries
