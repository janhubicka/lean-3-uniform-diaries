import ThreeUniformDiaries.RelativeCompletionIteratedLayers

/-!
# Finite prefixes of protected relative completion inside U

Successive selected layers of U form genuine finite rooted tree
pictures, with the same selected levels as the desired completion.
The protection invariant ensures prescribed E-nodes are not lost.
This file establishes the prefix bookkeeping prior to the
meet-closure induction (handled independently).
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The union of the first k+1 selected relative completion layers. -/
def relativeCompletionPrefix
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (E : Set CoordNode)
    (g : Nat → Nat) (hg : StrictMono g)
    (r : CoordNode) (k : Nat) : Set CoordNode :=
  {z | ∃ i : Nat, i ≤ k ∧
    z ∈ relativeCompletionLayers hU E g hg r i}

/-- The next prefix is the previous prefix plus its next layer. -/
theorem relativeCompletionPrefix_succ_iff
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (E : Set CoordNode)
    (g : Nat → Nat) (hg : StrictMono g)
    (r : CoordNode) (k : Nat) (z : CoordNode) :
    z ∈ relativeCompletionPrefix hU E g hg r (k + 1) ↔
      z ∈ relativeCompletionPrefix hU E g hg r k ∨
      z ∈ relativeCompletionLayers hU E g hg r (k + 1) := by
  constructor
  · rintro ⟨i, hi, hzi⟩
    by_cases hik : i ≤ k
    · exact Or.inl ⟨i, hik, hzi⟩
    · have hieq : i = k + 1 := by omega
      exact Or.inr (by simpa only [hieq] using hzi)
  · intro h
    rcases h with ⟨i, hi, hzi⟩ | hzi
    · exact ⟨i, by omega, hzi⟩
    · exact ⟨k + 1, le_rfl, hzi⟩

/-- The family of finite prefixes is nested. -/
theorem relativeCompletionPrefix_mono
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (E : Set CoordNode)
    (g : Nat → Nat) (hg : StrictMono g)
    (r : CoordNode) (i j : Nat) (hij : i ≤ j) :
    relativeCompletionPrefix hU E g hg r i ⊆
      relativeCompletionPrefix hU E g hg r j := by
  rintro z ⟨k, hki, hz⟩
  exact ⟨k, hki.trans hij, hz⟩

/-- The root stays below every chosen node in every relative layer. -/
theorem relativeCompletionLayers_root_le
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f)
    (E : Set CoordNode)
    (g : Nat → Nat) (hg : StrictMono g)
    (r : CoordNode) :
    ∀ (k : Nat) (z : CoordNode),
      z ∈ relativeCompletionLayers hU E g hg r k → r ≤ z := by
  intro k
  induction k with
  | zero =>
      intro z hz
      change z ∈ ({r} : Set CoordNode) at hz
      have hzr : z = r := by simpa using hz
      subst z
      exact le_refl r
  | succ k ih =>
      intro z hz
      obtain ⟨p, hp, hpz⟩ :=
        relativeCompletionLayers_has_parent hU hf E g hg r k z hz
      exact le_trans (ih p hp) hpz

/-- Every relative prefix remains above the original chosen root. -/
theorem relativeCompletionPrefix_root_le
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f)
    (E : Set CoordNode)
    (g : Nat → Nat) (hg : StrictMono g)
    (r : CoordNode) (k : Nat)
    (z : CoordNode)
    (hz : z ∈ relativeCompletionPrefix hU E g hg r k) :
    r ≤ z := by
  rcases hz with ⟨i, _, hzi⟩
  exact relativeCompletionLayers_root_le hU hf E g hg r i z hzi

/-- The root is present in every nonempty-height prefix. -/
theorem relativeCompletionPrefix_root_mem
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (E : Set CoordNode)
    (g : Nat → Nat) (hg : StrictMono g)
    (r : CoordNode) (k : Nat) :
    r ∈ relativeCompletionPrefix hU E g hg r k := by
  exact ⟨0, Nat.zero_le k, by simp [relativeCompletionLayers]⟩

/-- The protected relative completion never leaves U. -/
theorem relativeCompletionPrefix_subset
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f) (hrootLevel : level root = f 0)
    (E : Set CoordNode) (hEU : E ⊆ U)
    (g : Nat → Nat) (hg : StrictMono g)
    (r : CoordNode) (hr : r ∈ U)
    (k : Nat) :
    relativeCompletionPrefix hU E g hg r k ⊆ U := by
  rintro z ⟨i, _, hi⟩
  exact (relativeCompletionLayers_subset hU hf hrootLevel
    E hEU g hg r hr i) hi

/-- Every prefix node lies at one of the prescribed levels. -/
theorem relativeCompletionPrefix_selected_level
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (E : Set CoordNode)
    (g : Nat → Nat) (hg : StrictMono g)
    (r : CoordNode) (hrLevel : level r = f (g 0))
    (k : Nat) (z : CoordNode)
    (hz : z ∈ relativeCompletionPrefix hU E g hg r k) :
    ∃ i : Nat, i ≤ k ∧ level z = f (g i) := by
  rcases hz with ⟨i, hi, hzi⟩
  exact ⟨i, hi,
    relativeCompletionLayers_level hU E g hg r hrLevel i z hzi⟩

/-- Every prefix is a finite set despite the ambient U being infinite. -/
theorem relativeCompletionPrefix_finite
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (E : Set CoordNode)
    (g : Nat → Nat) (hg : StrictMono g)
    (r : CoordNode) (k : Nat) :
    (relativeCompletionPrefix hU E g hg r k).Finite := by
  induction k with
  | zero =>
      apply (Set.finite_singleton r).subset
      rintro z ⟨i, hi, hzi⟩
      have hi0 : i = 0 := by omega
      subst i
      exact hzi
  | succ k ih =>
      have hfin :=
        ih.union (relativeCompletionLayers_finite hU E g hg r (k + 1))
      apply hfin.subset
      intro z hz
      rcases (relativeCompletionPrefix_succ_iff
        hU E g hg r k z).mp hz with h | h
      · exact Or.inl h
      · exact Or.inr h

/-- Any prefix point has ambient level no greater than the last
relative layer. -/
theorem relativeCompletionPrefix_level_le
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f) (E : Set CoordNode)
    (g : Nat → Nat) (hg : StrictMono g)
    (r : CoordNode) (hrLevel : level r = f (g 0))
    (k : Nat) (z : CoordNode)
    (hz : z ∈ relativeCompletionPrefix hU E g hg r k) :
    level z ≤ f (g k) := by
  obtain ⟨i, hi, hzi⟩ :=
    relativeCompletionPrefix_selected_level hU E g hg r hrLevel k z hz
  rw [hzi]
  exact hf.monotone (hg.monotone hi)

end CoordNode
end ThreeUniformDiaries
