import ThreeUniformDiaries.InfiniteStrongCompletion

/-!
# Selected ancestor closure inside an infinite strong coordinate picture

The manuscript's geometric composition lemma completes the
meet-closed image *inside* a given strong coordinate tree U.  The
first relative-tree interface is that every U-node has, literally
in U, its ancestor on every earlier selected U-level.

This property follows from the genuine geometric strong-picture
axioms, not from an additional closure axiom: choose the unique
next selected representative in the cone followed by a later
U-node, then use meet closure and the absence of intervening
selected levels to show that representative lies below that node.

In particular, the underlying U-tree may be compressed to its
relative levels without losing any initial segments.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- A selected strong-picture child in the cone of a later retained
node must be an ancestor of that node, not merely share its
immediate child cone. This is the geometric rigidity step needed
for viewing U with its relative level numbering. -/
theorem infiniteStrongPicture_next_selected_below
    {S : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hS : InfiniteStrongPicture S f root)
    (hf : StrictMono f)
    (i j : Nat) (hij : i + 1 ≤ j)
    (p x : CoordNode)
    (hp : p ∈ S) (hpLevel : level p = f i)
    (hx : x ∈ S) (hxLevel : level x = f j)
    (hpx : p ≤ x) :
    ∃ q : CoordNode, q ∈ S ∧
      level q = f (i + 1) ∧ q ≤ x := by
  have hfi : f i + 1 ≤ f (i + 1) :=
    Nat.succ_le_of_lt (hf (Nat.lt_succ_self i))
  have hfj : f (i + 1) ≤ f j := hf.monotone hij
  have hxAbove : f i + 1 ≤ level x := by omega
  let t := truncate x (f i + 1)
  have htLevel : level t = f i + 1 := by simp [t]
  have htx : t ≤ x := truncate_le x hxAbove
  have hsourceCut : truncate x (f i) = p := by
    simpa only [hpLevel] using hpx.2
  have hpt : p ≤ t := by
    refine ⟨by rw [hpLevel, htLevel]; omega, ?_⟩
    rw [hpLevel]
    change truncate (truncate x (f i + 1)) (f i) = p
    rw [truncate_truncate x (Nat.le_succ i)]
    exact hsourceCut
  have hcover : p ⋖ t := by
    apply SuccessorTree.LevelTree.covBy_of_le_level_succ hpt
    rw [hpLevel, htLevel]
  obtain ⟨q, ⟨hq, hql, htq⟩, _⟩ :=
    hS.next_child i p hp hpLevel t hcover
  have hcommon : ∃ c : CoordNode, c ≤ q ∧ c ≤ x :=
    ⟨t, htq, htx⟩
  have hmeetInS : meet q x ∈ S := hS.meet_closed hq hx
  obtain ⟨k, hkLevel⟩ := hS.selected_levels (meet q x) hmeetInS
  have htm : t ≤ meet q x := le_meet htq htx
  have hmq : meet q x ≤ q := meet_le_left hcommon
  have hmx : meet q x ≤ x := meet_le_right hcommon
  have hlow : f i < f k := by
    have hlev := level_le_of_le htm
    rw [htLevel, hkLevel] at hlev
    omega
  have hik : i < k := by
    by_contra hnot
    have hki : k ≤ i := Nat.le_of_not_gt hnot
    have hkl := hf.monotone hki
    omega
  have hhigh : f k ≤ f (i + 1) := by
    have hlev := level_le_of_le hmq
    rw [hkLevel, hql] at hlev
    exact hlev
  have hki1 : k ≤ i + 1 := by
    by_contra hnot
    have hlt : i + 1 < k := Nat.lt_of_not_ge hnot
    have hmono := hf hlt
    omega
  have hk : k = i + 1 := by omega
  have hsame : level (meet q x) = level q := by
    rw [hkLevel, hql, hk]
  have hmeetEq : meet q x = q :=
    eq_of_le_of_level_eq hmq hsame
  have hqx : q ≤ x := by
    simpa only [hmeetEq] using hmx
  exact ⟨q, hq, hql, hqx⟩

/-- Every earlier selected-level ancestor of any node in a genuine
infinite strong picture belongs to that picture, even when the
ambient level map skips arbitrarily many levels. -/
theorem infiniteStrongPicture_selected_truncate_mem
    {S : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hS : InfiniteStrongPicture S f root)
    (hf : StrictMono f) (hrootLevel : level root = f 0)
    (i : Nat) :
    ∀ (j : Nat), i ≤ j →
      ∀ (x : CoordNode), x ∈ S →
        level x = f j → truncate x (f i) ∈ S := by
  induction i with
  | zero =>
      intro j hij x hx hxLevel
      have hrootBelow := hS.root_le x hx
      have hrootEq : truncate x (f 0) = root := by
        simpa only [hrootLevel] using hrootBelow.2
      rw [hrootEq]
      exact hS.root_mem
  | succ i ih =>
      intro j hij x hx hxLevel
      have hi : i ≤ j := by omega
      have hp : truncate x (f i) ∈ S :=
        ih j hi x hx hxLevel
      have hpx : truncate x (f i) ≤ x :=
        truncate_le x (by rw [hxLevel]; exact hf.monotone hi)
      obtain ⟨q, hq, hql, hqx⟩ :=
        infiniteStrongPicture_next_selected_below hS hf
          i j hij (truncate x (f i)) x
          hp (by simp) hx hxLevel hpx
      have htr : truncate x (f (i + 1)) = q := by
        simpa only [hql] using hqx.2
      rw [htr]
      exact hq

end CoordNode
end ThreeUniformDiaries
