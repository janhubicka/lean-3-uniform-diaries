import ThreeUniformDiaries.FiniteCompletionIteratedLayers

/-!
# Canonical ancestors in the completed selected-level tree

Iterated protected layers yield a genuine levelled tree picture:
every selected upper node has a predecessor at every earlier selected
level, and that predecessor is unique. Consequently the finite
initial union of layers is finite and the chosen layer indices
really describe a tree rather than an unrelated sequence of sets.
These properties are independent of E's meet-closedness; the
protection argument uses that hypothesis separately.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Every selected node at level j has an ancestor at every
earlier selected level i ≤ j. -/
theorem completionLayers_ancestor
    (E : Set CoordNode)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (root : CoordNode)
    (i j : Nat) (hij : i ≤ j) :
    ∀ (z : CoordNode),
      z ∈ completionLayers E lambda hmono root j →
      ∃ p : CoordNode,
        p ∈ completionLayers E lambda hmono root i ∧ p ≤ z := by
  induction j, hij using Nat.le_induction with
  | base =>
      intro z hz
      exact ⟨z, hz, le_refl z⟩
  | succ j hle ih =>
      intro z hz
      obtain ⟨q, hq, hqz⟩ :=
        completionLayers_has_parent E lambda hmono root j z hz
      obtain ⟨p, hp, hpq⟩ := ih q hq
      exact ⟨p, hp, le_trans hpq hqz⟩

/-- Ancestors at a prescribed selected level are unique, because
predecessors of any node are linearly ordered and the levels agree. -/
theorem completionLayers_unique_ancestor
    (E : Set CoordNode)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (root : CoordNode) (hroot : level root = lambda 0)
    (i j : Nat) (hij : i ≤ j)
    (z : CoordNode)
    (hz : z ∈ completionLayers E lambda hmono root j) :
    ∃! p : CoordNode,
      p ∈ completionLayers E lambda hmono root i ∧ p ≤ z := by
  obtain ⟨p, hp, hpz⟩ :=
    completionLayers_ancestor E lambda hmono root i j hij z hz
  refine ⟨p, ⟨hp, hpz⟩, ?_⟩
  intro q ⟨hq, hqz⟩
  have hlevel : level p = level q := by
    rw [completionLayers_level E lambda hmono root hroot i p hp,
      completionLayers_level E lambda hmono root hroot i q hq]
  rcases lower_linear hpz hqz with hpq | hqp
  · exact (eq_of_le_of_level_eq hpq hlevel).symm
  · exact eq_of_le_of_level_eq hqp hlevel.symm

/-- All selected layers up to the given finite index. -/
def completionPrefix
    (E : Set CoordNode)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (root : CoordNode) (k : Nat) : Set CoordNode :=
  {z | ∃ i : Nat, i ≤ k ∧
    z ∈ completionLayers E lambda hmono root i}

/-- The first k+1 selected layers form a finite set of nodes. -/
theorem completionPrefix_finite
    (E : Set CoordNode)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (root : CoordNode) (k : Nat) :
    (completionPrefix E lambda hmono root k).Finite := by
  induction k with
  | zero =>
      apply (completionLayers_finite E lambda hmono root 0).subset
      intro z hz
      rcases hz with ⟨i, hi, hz⟩
      have heq : i = 0 := by omega
      subst i
      exact hz
  | succ k ih =>
      have hfin : (completionPrefix E lambda hmono root k ∪
          completionLayers E lambda hmono root (k + 1)).Finite :=
        ih.union (completionLayers_finite E lambda hmono root (k + 1))
      apply hfin.subset
      intro z hz
      rcases hz with ⟨i, hik, hiz⟩
      by_cases hi : i ≤ k
      · exact Or.inl ⟨i, hi, hiz⟩
      · have heq : i = k + 1 := by omega
        exact Or.inr (by simpa [heq] using hiz)

/-- The prescribed root is an ancestor of every selected node,
irrespective of its selected level. -/
theorem completionLayers_root_le
    (E : Set CoordNode)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (root : CoordNode) (k : Nat) (z : CoordNode)
    (hz : z ∈ completionLayers E lambda hmono root k) :
    root ≤ z := by
  obtain ⟨p, hp, hpz⟩ :=
    completionLayers_ancestor E lambda hmono root 0 k
      (Nat.zero_le k) z hz
  have heq : p = root := by
    change p ∈ ({root} : Set CoordNode) at hp
    simpa using hp
  rwa [heq] at hpz

end CoordNode
end ThreeUniformDiaries
