import ThreeUniformDiaries.TypeTrees

/-!
# The synchronized vector type tree

A node on level `n` is one enumeration node, one 1-type node, and one
aux-type node.  Its immediate-successor data are respectively a level-`n`
1-type, a level-`n` aux-type, and one Boolean bit.

This proves the exact predecessor/successor decomposition.  Thus the product
tree in the manuscript is a spherically finite dependent-alphabet tree with
alphabet `OneNode n × AuxNode n × Bool` on level `n`.
-/

namespace ThreeUniformDiaries

namespace AuxNode

def truncate {N : Nat} (a : AuxNode N) (l : Nat) : AuxNode l where
  bit i := if i < l then a.bit i else false
  support := by
    intro i hi
    rw [if_neg (Nat.not_lt.mpr hi)]

@[simp] theorem truncate_succ {n : Nat} (a : AuxNode n) (e : Bool) :
    (a.succ e).truncate n = a := by
  apply AuxNode.ext_bits
  funext i
  by_cases hi : i < n
  · have hine : i ≠ n := by omega
    simp [truncate, succ, hi, hine]
  · have hge : n ≤ i := Nat.le_of_not_gt hi
    have hz := a.support i hge
    by_cases hin : i = n
    · subst i
      simp [truncate, succ, hz]
    · simp [truncate, succ, hi, hin, hz]

@[simp] theorem succ_truncate_new {n : Nat} (a : AuxNode (n + 1)) :
    (a.truncate n).succ (a.bit n) = a := by
  apply AuxNode.ext_bits
  funext i
  by_cases hi : i < n
  · have hine : i ≠ n := by omega
    simp [truncate, succ, hi, hine]
  · by_cases hin : i = n
    · subst i
      simp [truncate, succ]
    · have hge : n + 1 ≤ i := by omega
      have hz := a.support i hge
      simp [truncate, succ, hi, hin, hz]

end AuxNode

namespace OneNode

def truncate {N : Nat} (a : OneNode N) (l : Nat) : OneNode l where
  pair i j := if j < l then a.pair i j else false
  support := by
    intro i j hbad
    by_cases hj : j < l
    · rw [if_pos hj]
      apply a.support i j
      intro hvalid
      exact hbad ⟨hvalid.1, hj⟩
    · rw [if_neg hj]

def boundaryAux {N : Nat} (a : OneNode N) (k : Nat) : AuxNode k where
  bit i := if i < k then a.pair i k else false
  support := by
    intro i hi
    rw [if_neg (Nat.not_lt.mpr hi)]

@[simp] theorem truncate_succ {n : Nat} (a : OneNode n) (c : AuxNode n) :
    (a.succ c).truncate n = a := by
  apply OneNode.ext_pairs
  funext i j
  by_cases hj : j < n
  · have hjne : j ≠ n := by omega
    simp [truncate, succ, hj, hjne]
  · have hbad : ¬ (i < j ∧ j < n) := by
      intro h
      exact hj h.2
    have hz := a.support i j hbad
    by_cases hjeq : j = n
    · subst j
      simp [truncate, hz]
    · simp [truncate, succ, hj, hjeq, hz]

@[simp] theorem boundaryAux_succ {n : Nat} (a : OneNode n) (c : AuxNode n) :
    (a.succ c).boundaryAux n = c := by
  apply AuxNode.ext_bits
  funext i
  by_cases hi : i < n
  · simp [boundaryAux, succ, hi]
  · have hci := c.support i (Nat.le_of_not_gt hi)
    simp [boundaryAux, succ, hi, hci]

@[simp] theorem succ_truncate_boundary {n : Nat} (a : OneNode (n + 1)) :
    (a.truncate n).succ (a.boundaryAux n) = a := by
  apply OneNode.ext_pairs
  funext i j
  by_cases hj : j < n
  · have hjne : j ≠ n := by omega
    simp [truncate, boundaryAux, succ, hj, hjne]
  · by_cases hjeq : j = n
    · subst j
      by_cases hi : i < n
      · simp [truncate, boundaryAux, succ, hi]
      · have hbad : ¬ (i < n ∧ n < n + 1) := by
          intro h
          exact hi h.1
        have hz := a.support i n hbad
        simp [truncate, boundaryAux, succ, hi, hz]
    · have hbad : ¬ (i < j ∧ j < n + 1) := by omega
      have hz := a.support i j hbad
      simp [truncate, boundaryAux, succ, hj, hjeq, hz]

end OneNode

namespace EnumNode

def boundaryOne {N : Nat} (H : EnumNode N) (k : Nat) : OneNode k where
  pair i j := if i < j ∧ j < k then H.triple i j k else false
  support := by
    intro i j hbad
    rw [if_neg hbad]

@[simp] theorem truncate_succ {n : Nat} (H : EnumNode n) (b : OneNode n) :
    (H.succ b).truncate n = H := by
  apply EnumNode.ext_triples
  funext i j k
  by_cases hk : k < n
  · have hkne : k ≠ n := by omega
    simp [truncate, succ, hk, hkne]
  · have hbad : ¬ (i < j ∧ j < k ∧ k < n) := by
      intro h
      exact hk h.2.2
    have hz := H.support i j k hbad
    by_cases hkeq : k = n
    · subst k
      simp [truncate, hz]
    · simp [truncate, succ, hk, hkeq, hz]

@[simp] theorem boundaryOne_succ {n : Nat} (H : EnumNode n) (b : OneNode n) :
    (H.succ b).boundaryOne n = b := by
  apply OneNode.ext_pairs
  funext i j
  by_cases hv : i < j ∧ j < n
  · simp [boundaryOne, succ, hv]
  · have hb := b.support i j hv
    simp [boundaryOne, succ, hv, hb]

@[simp] theorem succ_truncate_boundary {n : Nat} (H : EnumNode (n + 1)) :
    (H.truncate n).succ (H.boundaryOne n) = H := by
  apply EnumNode.ext_triples
  funext i j k
  by_cases hk : k < n
  · have hkne : k ≠ n := by omega
    simp [truncate, boundaryOne, succ, hk, hkne]
  · by_cases hkeq : k = n
    · subst k
      by_cases hv : i < j ∧ j < n
      · simp [truncate, boundaryOne, succ, hv]
      · have hbad : ¬ (i < j ∧ j < n ∧ n < n + 1) := by
          intro h
          exact hv ⟨h.1, h.2.1⟩
        have hz := H.support i j n hbad
        simp [truncate, boundaryOne, succ, hv, hz]
    · have hbad : ¬ (i < j ∧ j < k ∧ k < n + 1) := by omega
      have hz := H.support i j k hbad
      simp [truncate, boundaryOne, succ, hk, hkeq, hz]

end EnumNode

structure VectorNode (n : Nat) where
  enum : EnumNode n
  one : OneNode n
  aux : AuxNode n

abbrev VectorStep (n : Nat) := OneNode n × AuxNode n × Bool

namespace VectorNode

def succ {n : Nat} (x : VectorNode n) (s : VectorStep n) :
    VectorNode (n + 1) where
  enum := x.enum.succ s.1
  one := x.one.succ s.2.1
  aux := x.aux.succ s.2.2

def pred {n : Nat} (x : VectorNode (n + 1)) : VectorNode n where
  enum := x.enum.truncate n
  one := x.one.truncate n
  aux := x.aux.truncate n

def lastStep {n : Nat} (x : VectorNode (n + 1)) : VectorStep n :=
  (x.enum.boundaryOne n, x.one.boundaryAux n, x.aux.bit n)

@[simp] theorem pred_succ {n : Nat} (x : VectorNode n) (s : VectorStep n) :
    (x.succ s).pred = x := by
  cases x
  rcases s with ⟨b, c, e⟩
  simp [succ, pred]

@[simp] theorem succ_pred_lastStep {n : Nat} (x : VectorNode (n + 1)) :
    x.pred.succ x.lastStep = x := by
  cases x
  simp [pred, succ, lastStep]

end VectorNode
end ThreeUniformDiaries
