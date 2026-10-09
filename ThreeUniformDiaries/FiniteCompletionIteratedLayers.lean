import ThreeUniformDiaries.FiniteCompletionNextLayer

/-!
# Iterate protected layers through a chosen level sequence

Starting at the root of a finite tree picture, repeat the protected
one-level completion. At each next selected level, every old child
cone receives exactly one chosen node. All layers stay finite.
Crucially, every E-node at a later selected level remains above some
chosen node, so at its own level it appears literally in the output.

The remaining global completion tasks are to assemble the layers into
a meet-closed strong subtree and to transport the finite encoding.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Protected finite layers indexed by an increasing sequence of
ambient levels. A finite strong subtree of height m uses k<m. -/
noncomputable def completionLayers
    (E : Set CoordNode)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (root : CoordNode) : Nat → Set CoordNode
  | 0 => {root}
  | k + 1 => nextLayer E
      (completionLayers E lambda hmono root k)
      (lambda k) (lambda (k + 1))
      (hmono (Nat.lt_succ_self k))

/-- Each completion layer is on exactly its prescribed ambient level. -/
theorem completionLayers_level
    (E : Set CoordNode)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (root : CoordNode) (hroot : level root = lambda 0)
    (k : Nat) (x : CoordNode)
    (hx : x ∈ completionLayers E lambda hmono root k) :
    level x = lambda k := by
  induction k with
  | zero =>
      change x ∈ ({root} : Set CoordNode) at hx
      have heq : x = root := by simpa using hx
      simpa [heq] using hroot
  | succ k ih =>
      change x ∈ nextLayer E
        (completionLayers E lambda hmono root k)
        (lambda k) (lambda (k + 1))
        (hmono (Nat.lt_succ_self k)) at hx
      exact nextLayer_level E
        (completionLayers E lambda hmono root k)
        (lambda k) (lambda (k + 1))
        (hmono (Nat.lt_succ_self k)) x hx

/-- Local finiteness of all finite approximations: no global
boundedness or finite E hypothesis is necessary. -/
theorem completionLayers_finite
    (E : Set CoordNode)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (root : CoordNode) (k : Nat) :
    (completionLayers E lambda hmono root k).Finite := by
  cases k with
  | zero =>
      change ({root} : Set CoordNode).Finite
      exact Set.finite_singleton root
  | succ k =>
      exact nextLayer_finite E
        (completionLayers E lambda hmono root k)
        (lambda k) (lambda (k + 1))
        (hmono (Nat.lt_succ_self k))

/-- Every child of every selected node has a unique representation
on the next selected level. This is the strong-branching condition. -/
theorem completionLayers_unique_child
    (E : Set CoordNode)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (root : CoordNode) (hroot : level root = lambda 0)
    (k : Nat) (p t : CoordNode)
    (hp : p ∈ completionLayers E lambda hmono root k)
    (hpt : p ⋖ t) :
    ∃! z : CoordNode,
      z ∈ completionLayers E lambda hmono root (k + 1) ∧
      t ≤ z := by
  change ∃! z : CoordNode,
    z ∈ nextLayer E
      (completionLayers E lambda hmono root k)
      (lambda k) (lambda (k + 1))
      (hmono (Nat.lt_succ_self k)) ∧ t ≤ z
  exact nextLayer_unique_child E
    (completionLayers E lambda hmono root k)
    (lambda k) (lambda (k + 1))
    (hmono (Nat.lt_succ_self k))
    p hp (completionLayers_level E lambda hmono root hroot k p hp)
    t hpt

/-- A chosen node on level k+1 always has a predecessor from level k
of the completed picture. -/
theorem completionLayers_has_parent
    (E : Set CoordNode)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (root : CoordNode) (k : Nat) (z : CoordNode)
    (hz : z ∈ completionLayers E lambda hmono root (k + 1)) :
    ∃ p : CoordNode,
      p ∈ completionLayers E lambda hmono root k ∧ p ≤ z := by
  change z ∈ nextLayer E
    (completionLayers E lambda hmono root k)
    (lambda k) (lambda (k + 1))
    (hmono (Nat.lt_succ_self k)) at hz
  rcases hz with ⟨g, rfl⟩
  exact ⟨g.parent, g.parent_mem,
    le_trans g.child_cover.le (g.chosen_extends E
      (lambda (k + 1)) (hmono (Nat.lt_succ_self k)))⟩

/-- The future-node protection invariant: every prescribed E-node
above level lambda k has a selected ancestor on that exact level.
The proof inducts through all earlier selected cuts. -/
theorem completionLayers_protects
    (E : Set CoordNode) (hE : MeetClosed E)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (hgap : ∀ k : Nat, AvoidsOpenLevelGap E
      (lambda k) (lambda (k + 1)))
    (root : CoordNode) (hrootLevel : level root = lambda 0)
    (hroot : ∀ x ∈ E, root ≤ x)
    (k : Nat) (x : CoordNode) (hx : x ∈ E)
    (hL : lambda k ≤ level x) :
    ∃ p : CoordNode,
      p ∈ completionLayers E lambda hmono root k ∧ p ≤ x := by
  induction k with
  | zero =>
      exact ⟨root, by simp [completionLayers], hroot x hx⟩
  | succ k ih =>
      have hprev : lambda k ≤ level x :=
        (hmono (Nat.lt_succ_self k)).le.trans hL
      rcases ih hprev with ⟨p, hp, hpx⟩
      have hpLevel : level p = lambda k :=
        completionLayers_level E lambda hmono root
          hrootLevel k p hp
      change ∃ z : CoordNode,
        z ∈ nextLayer E
          (completionLayers E lambda hmono root k)
          (lambda k) (lambda (k + 1))
          (hmono (Nat.lt_succ_self k)) ∧ z ≤ x
      exact nextLayer_protects E
        (completionLayers E lambda hmono root k) hE
        (lambda k) (lambda (k + 1))
        (hmono (Nat.lt_succ_self k)) (hgap k)
        p hp hpLevel x hx hpx hL

/-- Any prescribed E-node at a selected level is present *itself*,
not only represented by an isomorphic copy. -/
theorem completionLayers_contains_prescribed
    (E : Set CoordNode) (hE : MeetClosed E)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (hgap : ∀ k : Nat, AvoidsOpenLevelGap E
      (lambda k) (lambda (k + 1)))
    (root : CoordNode) (hrootLevel : level root = lambda 0)
    (hroot : ∀ x ∈ E, root ≤ x)
    (k : Nat) (x : CoordNode) (hx : x ∈ E)
    (hxLevel : level x = lambda k) :
    x ∈ completionLayers E lambda hmono root k := by
  obtain ⟨p, hp, hpx⟩ :=
    completionLayers_protects E hE lambda hmono hgap
      root hrootLevel hroot k x hx (by rw [hxLevel])
  have hpLevel := completionLayers_level E lambda hmono root
    hrootLevel k p hp
  have heq : p = x :=
    eq_of_le_of_level_eq hpx (hpLevel.trans hxLevel.symm)
  rw [← heq]
  exact hp

end CoordNode
end ThreeUniformDiaries
