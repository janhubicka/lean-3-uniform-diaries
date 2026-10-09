import ThreeUniformDiaries.FiniteCompletionConeChoice

/-!
# Finite completion: saturate one selected level

Given selected parent-level nodes P at level l and the next selected
level L>l, complete *every* immediate successor cone at level L.
Each cone receives a protected choice (guided by higher prescribed
nodes if present, and zero-extended otherwise).

The resulting layer is finite, all of its nodes are at L, and every
child cone of every old selected parent contains a unique chosen
node. No choice made at this step loses a prescribed later E-node.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- One immediate-successor direction of a selected parent layer. -/
structure GapChild (P : Set CoordNode) (l : Nat) where
  parent : CoordNode
  parent_mem : parent ∈ P
  parent_level : level parent = l
  child : CoordNode
  child_cover : parent ⋖ child

namespace GapChild

/-- The child is at level l+1, as in any levelled tree. -/
theorem child_level {P : Set CoordNode} {l : Nat}
    (g : GapChild P l) :
    level g.child = l + 1 := by
  rw [covBy_level g.child_cover, g.parent_level]

/-- The protected candidate extending a particular child cone at L. -/
noncomputable def chosen {P : Set CoordNode} {l : Nat}
    (g : GapChild P l) (E : Set CoordNode)
    (L : Nat) (hl : l < L) : CoordNode :=
  completionChoice E g.child L (by
    rw [g.child_level]
    omega)

theorem chosen_level {P : Set CoordNode} {l : Nat}
    (g : GapChild P l) (E : Set CoordNode)
    (L : Nat) (hl : l < L) :
    level (g.chosen E L hl) = L := by
  exact completionChoice_level E g.child L _

theorem chosen_extends {P : Set CoordNode} {l : Nat}
    (g : GapChild P l) (E : Set CoordNode)
    (L : Nat) (hl : l < L) :
    g.child ≤ g.chosen E L hl := by
  exact completionChoice_extends E g.child L _

end GapChild

/-- The next completed layer consists of one chosen node per ambient
child cone of the previous layer. -/
noncomputable def nextLayer
    (E P : Set CoordNode) (l L : Nat) (hl : l < L) :
    Set CoordNode :=
  Set.range (fun g : GapChild P l => g.chosen E L hl)

/-- Every node of the new layer lies on the prescribed target level. -/
theorem nextLayer_level
    (E P : Set CoordNode) (l L : Nat) (hl : l < L)
    (z : CoordNode) (hz : z ∈ nextLayer E P l L hl) :
    level z = L := by
  rcases hz with ⟨g, rfl⟩
  exact g.chosen_level E L hl

/-- No local finiteness hypothesis on P is needed: each ambient level
of CoordNode is itself finite. -/
theorem nextLayer_finite
    (E P : Set CoordNode) (l L : Nat) (hl : l < L) :
    (nextLayer E P l L hl).Finite := by
  apply (level_finite L).subset
  intro z hz
  exact nextLayer_level E P l L hl z hz

/-- Every child cone is represented exactly once in the next layer.
The uniqueness follows from lower-cone linearity at the same level
l+1, not from choosing any arbitrary enumeration of children. -/
theorem nextLayer_unique_child
    (E P : Set CoordNode) (l L : Nat) (hl : l < L)
    (p : CoordNode) (hp : p ∈ P) (hpLevel : level p = l)
    (t : CoordNode) (hpt : p ⋖ t) :
    ∃! z : CoordNode,
      z ∈ nextLayer E P l L hl ∧ t ≤ z := by
  let g : GapChild P l := ⟨p, hp, hpLevel, t, hpt⟩
  refine ⟨g.chosen E L hl, ?_, ?_⟩
  · exact ⟨⟨g, rfl⟩, g.chosen_extends E L hl⟩
  · intro z hz
    rcases hz with ⟨⟨g', hgz⟩, htz⟩
    subst z
    have htl : level t = l + 1 := by
      rw [covBy_level hpt, hpLevel]
    have hgl : level g'.child = l + 1 := g'.child_level
    have hchild : g'.child = t := by
      rcases lower_linear (g'.chosen_extends E L hl) htz with h | h
      · exact eq_of_le_of_level_eq h (by omega)
      · exact (eq_of_le_of_level_eq h (by omega)).symm
    change completionChoice E g'.child L _ =
      completionChoice E t L _
    rw [hchild]

/-- If a prescribed x lies above the next selected level and has a
parent p already in P at the previous selected level, the new layer
contains the unique cone guide below x. -/
theorem nextLayer_protects
    (E P : Set CoordNode) (hE : MeetClosed E)
    (l L : Nat) (hl : l < L)
    (hgap : AvoidsOpenLevelGap E l L)
    (p : CoordNode) (hp : p ∈ P) (hpLevel : level p = l)
    (x : CoordNode) (hx : x ∈ E)
    (hpx : p ≤ x) (hLx : L ≤ level x) :
    ∃ z : CoordNode,
      z ∈ nextLayer E P l L hl ∧ z ≤ x := by
  let t := truncate x (l + 1)
  have htLevel : level t = l + 1 := by simp [t]
  have htLeX : t ≤ x := truncate_le x (by omega)
  have hpLeT : p ≤ t := by
    refine ⟨by simpa [htLevel, hpLevel] using Nat.le_succ l, ?_⟩
    change truncate (truncate x (l + 1)) (level p) = p
    calc
      truncate (truncate x (l + 1)) (level p) =
          truncate x (level p) := truncate_truncate x (by omega)
      _ = p := hpx.2
  have hpt : p ⋖ t := by
    apply SuccessorTree.LevelTree.covBy_of_le_level_succ hpLeT
    omega
  let g : GapChild P l := ⟨p, hp, hpLevel, t, hpt⟩
  refine ⟨g.chosen E L hl, ⟨g, rfl⟩, ?_⟩
  exact completionChoice_below_prescribed E hE l L hgap
    t (by omega) (by omega) x hx htLeX hLx

/-- In particular, every prescribed node at level L is retained
literally, provided its level-l ancestor was already selected. -/
theorem nextLayer_contains_prescribed
    (E P : Set CoordNode) (hE : MeetClosed E)
    (l L : Nat) (hl : l < L)
    (hgap : AvoidsOpenLevelGap E l L)
    (p : CoordNode) (hp : p ∈ P) (hpLevel : level p = l)
    (x : CoordNode) (hx : x ∈ E)
    (hpx : p ≤ x) (hxL : level x = L) :
    x ∈ nextLayer E P l L hl := by
  obtain ⟨z, hz, hzx⟩ :=
    nextLayer_protects E P hE l L hl hgap
      p hp hpLevel x hx hpx (by omega)
  have hzL := nextLayer_level E P l L hl z hz
  have heq : z = x :=
    eq_of_le_of_level_eq hzx (hzL.trans hxL.symm)
  rw [← heq]
  exact hz

end CoordNode
end ThreeUniformDiaries
