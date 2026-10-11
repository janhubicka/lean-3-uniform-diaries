import ThreeUniformDiaries.InfiniteStrongSelectedAncestors

/-!
# Relative levels and pruning inside an infinite strong coordinate tree

For a genuine strong picture U on a strict selected ambient level map f,
every node x∈U occupies a unique relative level i with level x = f i.
We expose that index as a concrete function and verify its order laws.

Selected ancestor closure was established separately using meet
closure and strong successor cones. Pruning is also intrinsic:
at every retained node, the unique selected representative above a
canonical zero child can be iterated to arbitrary later relative levels.

Together these facts are the elementary interface needed to apply
protected strong completion inside U rather than only inside the
ambient coordinate tree.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Relative index of a node in a strong selected-level coordinate picture. -/
noncomputable def strongRelativeIndex
    {S : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hS : InfiniteStrongPicture S f root)
    (x : CoordNode) (hx : x ∈ S) : Nat :=
  Classical.choose (hS.selected_levels x hx)

/-- A selected node lives exactly on its relative ambient level. -/
theorem strongRelativeIndex_spec
    {S : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hS : InfiniteStrongPicture S f root)
    (x : CoordNode) (hx : x ∈ S) :
    level x = f (strongRelativeIndex hS x hx) :=
  Classical.choose_spec (hS.selected_levels x hx)

/-- Relative indices are unique for nodes on the same selected level. -/
theorem strongRelativeIndex_eq_of_level_eq
    {S : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hS : InfiniteStrongPicture S f root)
    (hf : StrictMono f)
    (x y : CoordNode) (hx : x ∈ S) (hy : y ∈ S)
    (hlevel : level x = level y) :
    strongRelativeIndex hS x hx = strongRelativeIndex hS y hy := by
  apply hf.injective
  calc
    f (strongRelativeIndex hS x hx) = level x :=
      (strongRelativeIndex_spec hS x hx).symm
    _ = level y := hlevel
    _ = f (strongRelativeIndex hS y hy) :=
      strongRelativeIndex_spec hS y hy

/-- The coordinate ancestor order is monotone in relative level. -/
theorem strongRelativeIndex_mono
    {S : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hS : InfiniteStrongPicture S f root)
    (hf : StrictMono f)
    (x y : CoordNode) (hx : x ∈ S) (hy : y ∈ S)
    (hxy : x ≤ y) :
    strongRelativeIndex hS x hx ≤ strongRelativeIndex hS y hy := by
  have hxLev := strongRelativeIndex_spec hS x hx
  have hyLev := strongRelativeIndex_spec hS y hy
  have hle := level_le_of_le hxy
  by_contra hnot
  have hrev :
      strongRelativeIndex hS y hy < strongRelativeIndex hS x hx :=
    Nat.lt_of_not_ge hnot
  have hstrict := hf hrev
  omega

/-- Strict ancestor relations strictly increase the relative index. -/
theorem strongRelativeIndex_strictMono
    {S : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hS : InfiniteStrongPicture S f root)
    (hf : StrictMono f)
    (x y : CoordNode) (hx : x ∈ S) (hy : y ∈ S)
    (hxy : x < y) :
    strongRelativeIndex hS x hx < strongRelativeIndex hS y hy := by
  have hxLev := strongRelativeIndex_spec hS x hx
  have hyLev := strongRelativeIndex_spec hS y hy
  have hlt := level_lt_of_lt hxy
  by_contra hnot
  have hrev :
      strongRelativeIndex hS y hy ≤ strongRelativeIndex hS x hx :=
    Nat.le_of_not_gt hnot
  have hmono := hf.monotone hrev
  omega

/-- Truncation to the i-th selected level has relative index i. -/
theorem strongRelativeIndex_truncate
    {S : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hS : InfiniteStrongPicture S f root)
    (hf : StrictMono f) (hrootLevel : level root = f 0)
    (i j : Nat) (hij : i ≤ j)
    (x : CoordNode) (hx : x ∈ S) (hxLevel : level x = f j) :
    let hp := infiniteStrongPicture_selected_truncate_mem
      hS hf hrootLevel i j hij x hx hxLevel
    strongRelativeIndex hS (truncate x (f i)) hp = i := by
  dsimp only
  apply hf.injective
  calc
    f (strongRelativeIndex hS (truncate x (f i))
      (infiniteStrongPicture_selected_truncate_mem
        hS hf hrootLevel i j hij x hx hxLevel)) =
      level (truncate x (f i)) := by
        exact (strongRelativeIndex_spec hS _ _).symm
    _ = f i := by simp

/-- Every selected node has a selected successor at the next relative
level: take the strong representative of its canonical zero child. -/
theorem infiniteStrongPicture_next_relative_exists
    {S : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hS : InfiniteStrongPicture S f root)
    (i : Nat) (p : CoordNode)
    (hp : p ∈ S) (hpLevel : level p = f i) :
    ∃ z : CoordNode, z ∈ S ∧ level z = f (i + 1) ∧ p ≤ z := by
  have hpChild : p ⋖ zeroChild p := by
    apply SuccessorTree.LevelTree.covBy_of_le_level_succ
      (le_zeroChild p)
    exact level_zeroChild p
  obtain ⟨z, ⟨hz, hzlevel, htz⟩, _⟩ :=
    hS.next_child i p hp hpLevel (zeroChild p) hpChild
  exact ⟨z, hz, hzlevel, le_trans (le_zeroChild p) htz⟩

/-- Every selected node can be extended to every later selected
relative level, so the relative coordinate tree is pruned. -/
theorem infiniteStrongPicture_later_relative_exists
    {S : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hS : InfiniteStrongPicture S f root)
    (i j : Nat) (hij : i ≤ j) (p : CoordNode)
    (hp : p ∈ S) (hpLevel : level p = f i) :
    ∃ z : CoordNode, z ∈ S ∧ level z = f j ∧ p ≤ z := by
  induction j, hij using Nat.le_induction with
  | base =>
      exact ⟨p, hp, hpLevel, le_refl p⟩
  | succ j hle ih =>
      obtain ⟨q, hq, hql, hpq⟩ := ih
      obtain ⟨z, hz, hzl, hqz⟩ :=
        infiniteStrongPicture_next_relative_exists hS j q hq hql
      exact ⟨z, hz, hzl, le_trans hpq hqz⟩

end CoordNode
end ThreeUniformDiaries
