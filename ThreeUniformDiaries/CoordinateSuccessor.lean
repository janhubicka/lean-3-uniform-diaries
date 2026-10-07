import ThreeUniformDiaries.CoordinateTree
import SuccessorTree.Successor

/-!
# Successor operation on the three type trees

The apparent same-level parameters in the manuscript are decomposed one step
further so that they satisfy the strict parameter-level requirement of the
successor-tree formalization.

* an aux-type successor carries one Boolean label;
* a 1-type successor at level n+1 carries the level-n predecessor of its
  aux-type parameter and the last Boolean bit;
* an enumeration successor at level n+1 carries the level-n predecessors
  which reconstruct its 1-type parameter.

This is exactly the recursive dependency T2 -> T1 -> T0.
-/

namespace ThreeUniformDiaries

open SuccessorTree

namespace AuxNode

def root : AuxNode 0 where
  bit := fun _ => false
  support := by intro i hi; rfl

@[simp] theorem eq_root (a : AuxNode 0) : a = root := by
  apply AuxNode.ext_bits
  funext i
  exact a.support i (Nat.zero_le i)

end AuxNode

namespace OneNode

def root : OneNode 0 where
  pair := fun _ _ => false
  support := by intro i j h; rfl

@[simp] theorem eq_root (a : OneNode 0) : a = root := by
  apply OneNode.ext_pairs
  funext i j
  apply a.support i j
  omega

end OneNode

namespace EnumNode

def root : EnumNode 0 where
  triple := fun _ _ _ => false
  support := by intro i j k h; rfl

@[simp] theorem eq_root (a : EnumNode 0) : a = root := by
  apply EnumNode.ext_triples
  funext i j k
  apply a.support i j k
  omega

end EnumNode

inductive CoordLabel where
  | auxBit (e : Bool)
  | oneBit (e : Bool)
  | enum

namespace CoordNode

/-- The successor operation after recursively decomposing same-level
parameters into lower-level parameters plus a finite label. -/
def succ : CoordNode → List CoordNode → CoordLabel → Option CoordNode
  | .aux n a, [], .auxBit e =>
      some (.aux (n + 1) (a.succ e))
  | .one 0 a, [], .oneBit false =>
      some (.one 1 (a.succ AuxNode.root))
  | .one (n + 1) a, [.aux n c], .oneBit e =>
      some (.one (n + 2) (a.succ (c.succ e)))
  | .enum 0 a, [], .enum =>
      some (.enum 1 (a.succ OneNode.root))
  | .enum (n + 1) a, [.one n b, .aux n c], .enum =>
      some (.enum (n + 2) (a.succ (b.succ c)))
  | _, _, _ => none

/-- Parameters determined by the incoming edge of a non-root node. -/
def incomingParams : CoordNode → List CoordNode
  | .aux _ _ => []
  | .one 0 _ => []
  | .one 1 _ => []
  | .one (n + 2) a =>
      let c := a.boundaryAux (n + 1)
      [.aux n (c.truncate n)]
  | .enum 0 _ => []
  | .enum 1 _ => []
  | .enum (n + 2) a =>
      let b := a.boundaryOne (n + 1)
      [.one n (b.truncate n), .aux n (b.boundaryAux n)]

/-- Label determined by the incoming edge of a non-root node. -/
def incomingLabel : CoordNode → CoordLabel
  | .aux 0 _ => .auxBit false
  | .aux (n + 1) a => .auxBit (a.bit n)
  | .one 0 _ => .oneBit false
  | .one 1 _ => .oneBit false
  | .one (n + 2) a =>
      .oneBit ((a.boundaryAux (n + 1)).bit n)
  | .enum _ _ => .enum

theorem succ_incoming (x : CoordNode) (hx : 0 < level x) :
    succ (truncate x (level x - 1)) (incomingParams x) (incomingLabel x) =
      some x := by
  cases x with
  | aux m a =>
      cases m with
      | zero => simp [level] at hx
      | succ n =>
          simp [level, truncate, incomingParams, incomingLabel, succ,
            AuxNode.succ_truncate_new]
  | one m a =>
      cases m with
      | zero => simp [level] at hx
      | succ n =>
          cases n with
          | zero =>
              have hc : a.boundaryAux 0 = AuxNode.root := by simp
              simp [level, truncate, incomingParams, incomingLabel, succ, hc,
                OneNode.succ_truncate_boundary]
          | succ k =>
              let c := a.boundaryAux (k + 1)
              have hc :
                  (c.truncate k).succ (c.bit k) = c := by
                simpa [c] using AuxNode.succ_truncate_new c
              simp [level, truncate, incomingParams, incomingLabel, succ, c,
                hc, OneNode.succ_truncate_boundary]
  | enum m a =>
      cases m with
      | zero => simp [level] at hx
      | succ n =>
          cases n with
          | zero =>
              have hb : a.boundaryOne 0 = OneNode.root := by simp
              simp [level, truncate, incomingParams, incomingLabel, succ, hb,
                EnumNode.succ_truncate_boundary]
          | succ k =>
              let b := a.boundaryOne (k + 1)
              have hb :
                  (b.truncate k).succ (b.boundaryAux k) = b := by
                simpa [b] using OneNode.succ_truncate_boundary b
              simp [level, truncate, incomingParams, incomingLabel, succ, b,
                hb, EnumNode.succ_truncate_boundary]

/-- Every defined successor remembers its base, parameters and label. -/
theorem succ_recover {a x : CoordNode} {p : List CoordNode} {c : CoordLabel}
    (h : succ a p c = some x) :
    level x = level a + 1 ∧
    truncate x (level a) = a ∧
    p = incomingParams x ∧
    c = incomingLabel x := by
  cases a with
  | aux n a =>
      cases p with
      | nil =>
          cases c with
          | auxBit e =>
              simp [succ] at h
              subst x
              simp [level, truncate, incomingParams, incomingLabel]
          | oneBit e => simp [succ] at h
          | enum => simp [succ] at h
      | cons q qs => simp [succ] at h
  | one n a =>
      cases n with
      | zero =>
          cases p with
          | nil =>
              cases c with
              | auxBit e => simp [succ] at h
              | oneBit e =>
                  cases e <;> simp [succ] at h
                  subst x
                  simp [level, truncate, incomingParams, incomingLabel]
              | enum => simp [succ] at h
          | cons q qs => simp [succ] at h
      | succ n =>
          cases p with
          | nil => simp [succ] at h
          | cons q qs =>
              cases qs with
              | nil =>
                  cases q with
                  | aux m q =>
                      cases c with
                      | auxBit e => simp [succ] at h
                      | oneBit e =>
                          by_cases hm : m = n
                          · subst m
                            simp [succ] at h
                            subst x
                            simp [level, truncate, incomingParams,
                              incomingLabel, AuxNode.boundaryAux_succ]
                          · simp [succ, hm] at h
                      | enum => simp [succ] at h
                  | one m q => simp [succ] at h
                  | enum m q => simp [succ] at h
              | cons q' qs' => simp [succ] at h
  | enum n a =>
      cases n with
      | zero =>
          cases p with
          | nil =>
              cases c with
              | auxBit e => simp [succ] at h
              | oneBit e => simp [succ] at h
              | enum =>
                  simp [succ] at h
                  subst x
                  simp [level, truncate, incomingParams, incomingLabel]
          | cons q qs => simp [succ] at h
      | succ n =>
          cases p with
          | nil => simp [succ] at h
          | cons q qs =>
              cases qs with
              | nil => simp [succ] at h
              | cons r rs =>
                  cases rs with
                  | nil =>
                      cases q with
                      | aux m q => simp [succ] at h
                      | enum m q => simp [succ] at h
                      | one m q =>
                          cases r with
                          | one l r => simp [succ] at h
                          | enum l r => simp [succ] at h
                          | aux l r =>
                              cases c with
                              | auxBit e => simp [succ] at h
                              | oneBit e => simp [succ] at h
                              | enum =>
                                  by_cases hm : m = n
                                  · subst m
                                    by_cases hl : l = n
                                    · subst l
                                      simp [succ] at h
                                      subst x
                                      simp [level, truncate, incomingParams,
                                        incomingLabel,
                                        OneNode.boundaryAux_succ,
                                        EnumNode.boundaryOne_succ]
                                    · simp [succ, hl] at h
                                  · simp [succ, hm] at h
                  | cons s ss => simp [succ] at h

theorem incoming_param_two_le {x y : CoordNode}
    (hy : y ∈ incomingParams x) :
    level y + 2 ≤ level x := by
  cases x with
  | aux n a => simp [incomingParams] at hy
  | one n a =>
      cases n with
      | zero => simp [incomingParams] at hy
      | succ n =>
          cases n with
          | zero => simp [incomingParams] at hy
          | succ k =>
              simp [incomingParams] at hy
              rcases hy with rfl
              simp [level]
  | enum n a =>
      cases n with
      | zero => simp [incomingParams] at hy
      | succ n =>
          cases n with
          | zero => simp [incomingParams] at hy
          | succ k =>
              simp [incomingParams] at hy
              rcases hy with rfl | rfl
              · simp [level]
              · simp [level]

/-- The three type trees, regarded as one successor tree. -/
noncomputable def typeSTree : STree CoordNode CoordLabel where
  succ := succ
  s1 := by
    intro a p c x h
    have hr := succ_recover h
    constructor
    · apply LevelTree.covBy_of_le_level_succ
      · exact ⟨by omega, hr.2.1⟩
      · exact hr.1
    · intro y hy
      rw [hr.2.2.1] at hy
      have hp := incoming_param_two_le hy
      omega
  s2 := by
    intro a b x p q c d ha hb
    have hra := succ_recover ha
    have hrb := succ_recover hb
    have hlevel : level a = level b := by omega
    have hab : a = b := by
      calc
        a = truncate x (level a) := hra.2.1.symm
        _ = truncate x (level b) := by rw [hlevel]
        _ = b := hrb.2.1
    subst b
    exact ⟨rfl,
      hra.2.2.1.trans hrb.2.2.1.symm,
      hra.2.2.2.trans hrb.2.2.2.symm⟩
  s3 := by
    intro a x hax
    have hlevel : level x = level a + 1 :=
      LevelTree.covBy_level_eq hax
    have hxpos : 0 < level x := by omega
    refine ⟨incomingParams x, incomingLabel x, ?_⟩
    have hs := succ_incoming x hxpos
    have hpred : truncate x (level x - 1) = a := by
      have hsub : level x - 1 = level a := by omega
      rw [hsub]
      exact hax.le.2
    rw [hpred] at hs
    exact hs

end CoordNode
end ThreeUniformDiaries
