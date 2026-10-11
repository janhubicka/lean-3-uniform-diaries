import ThreeUniformDiaries.RootGluedTreeOrder

/-!
# Rigidity of the three level-zero cones of the root-glued type tree

There is exactly one level-zero node in each coordinate sort E0,E1,E2.
Thus every scalar immediate child of the newly adjoined root is
the initial-segment ancestor of every deeper node in its sort.

This is the actual three-way root branching lemma needed when
turning synchronized vector strong trees into scalar strong trees.
It does not rely on any non-homogeneous Milliken conclusion.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem auxNode_zero_unique (a b : AuxNode 0) : a = b := by
  apply AuxNode.ext_bits
  funext i
  exact (a.support i (Nat.zero_le i)).trans
    (b.support i (Nat.zero_le i)).symm

theorem oneNode_zero_unique (a b : OneNode 0) : a = b := by
  apply OneNode.ext_pairs
  funext i j
  have hbad : ¬ (i < j ∧ j < 0) := by omega
  exact (a.support i j hbad).trans (b.support i j hbad).symm

theorem enumNode_zero_unique (a b : EnumNode 0) : a = b := by
  apply EnumNode.ext_triples
  funext i j k
  have hbad : ¬ (i < j ∧ j < k ∧ k < 0) := by omega
  exact (a.support i j k hbad).trans (b.support i j k hbad).symm

/-- Ancestors remain in the same type-tree coordinate. -/
theorem sort_eq_of_le {x y : CoordNode} (hxy : x ≤ y) :
    sort x = sort y := by
  have h := hxy.2
  change truncate y (level x) = x at h
  rw [← h]
  cases y <;> rfl

theorem sort_truncate (x : CoordNode) (j : Nat) :
    sort (truncate x j) = sort x := by
  cases x <;> rfl

/-- There is at most one node in each of the three distinct
coordinate cones at ambient level zero. -/
theorem unique_zero_node_of_same_sort
    (x y : CoordNode)
    (hx : level x = 0) (hy : level y = 0)
    (hsort : sort x = sort y) : x = y := by
  cases x with
  | aux n a =>
      cases y with
      | aux m b =>
          have hn : n = 0 := hx
          have hm : m = 0 := hy
          subst n
          subst m
          exact congrArg (CoordNode.aux 0) (auxNode_zero_unique a b)
      | one m b => simp [sort] at hsort
      | enum m b => simp [sort] at hsort
  | one n a =>
      cases y with
      | aux m b => simp [sort] at hsort
      | one m b =>
          have hn : n = 0 := hx
          have hm : m = 0 := hy
          subst n
          subst m
          exact congrArg (CoordNode.one 0) (oneNode_zero_unique a b)
      | enum m b => simp [sort] at hsort
  | enum n a =>
      cases y with
      | aux m b => simp [sort] at hsort
      | one m b => simp [sort] at hsort
      | enum m b =>
          have hn : n = 0 := hx
          have hm : m = 0 := hy
          subst n
          subst m
          exact congrArg (CoordNode.enum 0) (enumNode_zero_unique a b)

/-- Any node is above the unique level-zero vertex of its sort. -/
theorem zero_node_le_of_same_sort
    (x y : CoordNode)
    (hx : level x = 0)
    (hsort : sort x = sort y) :
    x ≤ y := by
  have hzero : level (truncate y 0) = 0 := by simp
  have hsort' : sort x = sort (truncate y 0) := by
    rw [sort_truncate y 0]
    exact hsort
  have heq : x = truncate y 0 :=
    unique_zero_node_of_same_sort x (truncate y 0)
      hx hzero hsort'
  refine ⟨by rw [hx]; omega, ?_⟩
  rw [hx]
  exact heq.symm

/-- The three immediate cones above the new scalar root agree
with the three type-tree coordinate sorts. -/
theorem glued_root_child_below_iff_sort
    (x y : CoordNode)
    (hx : gluedChild none (some x)) :
    gluedLE (some x) (some y) ↔ sort x = sort y := by
  change level x = 0 at hx
  change x ≤ y ↔ sort x = sort y
  exact ⟨fun h => sort_eq_of_le h,
    fun h => zero_node_le_of_same_sort x y hx h⟩

end CoordNode
end ThreeUniformDiaries
