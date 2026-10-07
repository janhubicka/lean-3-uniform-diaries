import ThreeUniformDiaries.VectorTree
import SuccessorTree.Tree
import Mathlib.Data.Nat.Find

/-!
# The levelled forest of the three type trees

The three coordinates are kept as three connected components of one
levelled forest.  Order is initial-segment order, implemented by truncation.
This is the tree on which the successor-tree backend will act.

The meet field is only required by `SuccessorTree.LevelTree` when a common
predecessor exists.  In that case we take the greatest level on which the two
truncations agree.
-/

namespace ThreeUniformDiaries

open SuccessorTree

inductive CoordNode where
  | aux (n : Nat) (node : AuxNode n)
  | one (n : Nat) (node : OneNode n)
  | enum (n : Nat) (node : EnumNode n)

namespace CoordNode

def level : CoordNode → Nat
  | .aux n _ => n
  | .one n _ => n
  | .enum n _ => n

def truncate : CoordNode → (k : Nat) → CoordNode
  | .aux _ a, k => .aux k (a.truncate k)
  | .one _ a, k => .one k (a.truncate k)
  | .enum _ a, k => .enum k (a.truncate k)

@[simp] theorem level_truncate (x : CoordNode) (k : Nat) :
    level (truncate x k) = k := by
  cases x <;> rfl

@[simp] theorem truncate_self (x : CoordNode) :
    truncate x (level x) = x := by
  cases x with
  | aux n a => simp [truncate, level]
  | one n a => simp [truncate, level]
  | enum n a => simp [truncate, level]

theorem truncate_truncate (x : CoordNode) {k l : Nat} (hkl : k ≤ l) :
    truncate (truncate x l) k = truncate x k := by
  cases x with
  | aux n a =>
      simp only [truncate]
      rw [AuxNode.truncate_truncate a hkl]
  | one n a =>
      simp only [truncate]
      rw [OneNode.truncate_truncate a hkl]
  | enum n a =>
      simp only [truncate]
      rw [EnumNode.truncate_truncate a hkl]

def PrefixLE (x y : CoordNode) : Prop :=
  level x ≤ level y ∧ truncate y (level x) = x

instance : _root_.LE CoordNode := ⟨PrefixLE⟩

@[simp] theorem le_def {x y : CoordNode} :
    x ≤ y ↔ level x ≤ level y ∧ truncate y (level x) = x :=
  Iff.rfl

theorem le_refl (x : CoordNode) : x ≤ x :=
  ⟨le_rfl, truncate_self x⟩

theorem le_trans {x y z : CoordNode} (hxy : x ≤ y) (hyz : y ≤ z) :
    x ≤ z := by
  refine ⟨hxy.1.trans hyz.1, ?_⟩
  calc
    truncate z (level x) =
        truncate (truncate z (level y)) (level x) := by
          symm
          exact truncate_truncate z hxy.1
    _ = truncate y (level x) := by rw [hyz.2]
    _ = x := hxy.2

theorem le_antisymm {x y : CoordNode} (hxy : x ≤ y) (hyx : y ≤ x) :
    x = y := by
  have hlev : level x = level y := Nat.le_antisymm hxy.1 hyx.1
  calc
    x = truncate y (level x) := hxy.2.symm
    _ = truncate y (level y) := by rw [hlev]
    _ = y := truncate_self y

instance : PartialOrder CoordNode where
  le := PrefixLE
  le_refl := fun x => CoordNode.le_refl x
  le_trans := by
    intro x y z hxy hyz
    exact CoordNode.le_trans hxy hyz
  le_antisymm := by
    intro x y hxy hyx
    exact CoordNode.le_antisymm hxy hyx

theorem level_le_of_le {x y : CoordNode} (h : x ≤ y) :
    level x ≤ level y :=
  h.1

theorem eq_of_le_of_level_eq {x y : CoordNode} (hxy : x ≤ y)
    (hlevel : level x = level y) :
    x = y := by
  calc
    x = truncate y (level x) := hxy.2.symm
    _ = truncate y (level y) := by rw [hlevel]
    _ = y := truncate_self y

theorem level_lt_of_lt {x y : CoordNode} (hxy : x < y) :
    level x < level y := by
  have hle : level x ≤ level y := hxy.le.1
  exact lt_of_le_of_ne hle (by
    intro heq
    exact hxy.ne (eq_of_le_of_level_eq hxy.le heq))

theorem truncate_le (x : CoordNode) {k : Nat} (hk : k ≤ level x) :
    truncate x k ≤ x := by
  refine ⟨?_, ?_⟩
  · simpa using hk
  · simp

theorem truncate_mono {x : CoordNode} {k l : Nat}
    (hkl : k ≤ l) (hl : l ≤ level x) :
    truncate x k ≤ truncate x l := by
  refine ⟨by simp [hkl], ?_⟩
  simp only [level_truncate]
  exact truncate_truncate x hkl

theorem lower_linear {a b c : CoordNode} (ha : a ≤ c) (hb : b ≤ c) :
    a ≤ b ∨ b ≤ a := by
  rcases le_total (level a) (level b) with hab | hba
  · left
    refine ⟨hab, ?_⟩
    calc
      truncate b (level a) =
          truncate (truncate c (level b)) (level a) := by rw [hb.2]
      _ = truncate c (level a) := truncate_truncate c hab
      _ = a := ha.2
  · right
    refine ⟨hba, ?_⟩
    calc
      truncate a (level b) =
          truncate (truncate c (level a)) (level b) := by rw [ha.2]
      _ = truncate c (level b) := truncate_truncate c hba
      _ = b := hb.2

theorem ancestor_exists (a : CoordNode) (n : Nat) (hn : n ≤ level a) :
    ∃ b : CoordNode, b ≤ a ∧ level b = n := by
  refine ⟨truncate a n, truncate_le a hn, ?_⟩
  simp

theorem level_finite (n : Nat) :
    Set.Finite {a : CoordNode | level a = n} := by
  classical
  let A : Set CoordNode := Set.range (fun a : AuxNode n => CoordNode.aux n a)
  let O : Set CoordNode := Set.range (fun a : OneNode n => CoordNode.one n a)
  let E : Set CoordNode := Set.range (fun a : EnumNode n => CoordNode.enum n a)
  have hA : A.Finite := Set.finite_range _
  have hO : O.Finite := Set.finite_range _
  have hE : E.Finite := Set.finite_range _
  apply (hA.union (hO.union hE)).subset
  intro x hx
  cases x with
  | aux m a =>
      have hm : m = n := by simpa [level] using hx
      subst m
      exact Set.mem_union_left _ ⟨a, rfl⟩
  | one m a =>
      have hm : m = n := by simpa [level] using hx
      subst m
      exact Set.mem_union_right _ (Set.mem_union_left _ ⟨a, rfl⟩)
  | enum m a =>
      have hm : m = n := by simpa [level] using hx
      subst m
      exact Set.mem_union_right _ (Set.mem_union_right _ ⟨a, rfl⟩)

def CommonAt (a b : CoordNode) (k : Nat) : Prop :=
  truncate a k = truncate b k

noncomputable def meetLevel (a b : CoordNode) : Nat := by
  classical
  exact Nat.findGreatest (CommonAt a b) (min (level a) (level b))

noncomputable def meet (a b : CoordNode) : CoordNode :=
  truncate a (meetLevel a b)

theorem commonAt_of_commonPred {a b c : CoordNode}
    (hca : c ≤ a) (hcb : c ≤ b) :
    CommonAt a b (level c) := by
  unfold CommonAt
  rw [hca.2, hcb.2]

theorem meetLevel_spec {a b : CoordNode}
    (hcommon : ∃ c : CoordNode, c ≤ a ∧ c ≤ b) :
    CommonAt a b (meetLevel a b) := by
  classical
  rcases hcommon with ⟨c, hca, hcb⟩
  apply Nat.findGreatest_spec
      (m := level c)
      (n := min (level a) (level b))
  · exact le_min hca.1 hcb.1
  · exact commonAt_of_commonPred hca hcb

theorem meetLevel_le_left (a b : CoordNode) :
    meetLevel a b ≤ level a := by
  classical
  exact (Nat.findGreatest_le (P := CommonAt a b)
    (min (level a) (level b))).trans (min_le_left _ _)

theorem meetLevel_le_right (a b : CoordNode) :
    meetLevel a b ≤ level b := by
  classical
  exact (Nat.findGreatest_le (P := CommonAt a b)
    (min (level a) (level b))).trans (min_le_right _ _)

theorem meet_le_left {a b : CoordNode}
    (hcommon : ∃ c : CoordNode, c ≤ a ∧ c ≤ b) :
    meet a b ≤ a := by
  unfold meet
  exact truncate_le a (meetLevel_le_left a b)

theorem meet_le_right {a b : CoordNode}
    (hcommon : ∃ c : CoordNode, c ≤ a ∧ c ≤ b) :
    meet a b ≤ b := by
  classical
  rw [le_def]
  simp only [meet, level_truncate]
  exact ⟨meetLevel_le_right a b, (meetLevel_spec hcommon).symm⟩

theorem le_meet {a b c : CoordNode} (hca : c ≤ a) (hcb : c ≤ b) :
    c ≤ meet a b := by
  classical
  have hcP : CommonAt a b (level c) :=
    commonAt_of_commonPred hca hcb
  have hcbound : level c ≤ min (level a) (level b) :=
    le_min hca.1 hcb.1
  have hcle : level c ≤ meetLevel a b :=
    Nat.le_findGreatest hcbound hcP
  refine ⟨by simpa [meet] using hcle, ?_⟩
  simp only [meet, level_truncate]
  calc
    truncate (truncate a (meetLevel a b)) (level c) =
        truncate a (level c) :=
      truncate_truncate a hcle
    _ = c := hca.2

theorem covBy_level {a b : CoordNode} (hab : a ⋖ b) :
    level b = level a + 1 := by
  have hlt : level a < level b := level_lt_of_lt hab.lt
  by_contra hne
  have hgap : level a + 1 < level b := by omega
  let z := truncate b (level a + 1)
  have hzb : z ≤ b := truncate_le b (by omega)
  have haz : a ≤ z := by
    refine ⟨by simp [z], ?_⟩
    simp only [z, level_truncate]
    calc
      truncate (truncate b (level a + 1)) (level a) =
          truncate b (level a) :=
        truncate_truncate b (by omega)
      _ = a := hab.le.2
  have hazlt : a < z := lt_of_le_of_ne haz (by
    intro h
    have hl := congrArg level h
    simp [z] at hl)
  have hzblt : z < b := lt_of_le_of_ne hzb (by
    intro h
    have hl := congrArg level h
    simp [z] at hl
    omega)
  exact (not_covBy_of_lt_of_lt hazlt hzblt) hab

noncomputable instance : LevelTree CoordNode where
  level := level
  level_lt := level_lt_of_lt
  covBy_level := covBy_level
  lower_linear := lower_linear
  ancestor_exists := ancestor_exists
  level_finite := level_finite
  meet := meet
  meet_le_left := meet_le_left
  meet_le_right := meet_le_right
  le_meet := le_meet

end CoordNode
end ThreeUniformDiaries
