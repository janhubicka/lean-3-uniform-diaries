import ThreeUniformDiaries.RootGluedCoordinateCarrier

/-!
# Exact set-level inverse of root-gluing

Every subset of the scalar root-glued tree that contains the new root
is uniquely the root-gluing of a typed vector subset of the three
coordinate type trees. No scalar nodes are lost and no two distinct
coordinate subsets collapse to the same scalar set.

This is the carrier half of the finite and infinite strong-subtree
bijections required for applying non-homogeneous Milliken.
Strongness itself is not bundled in this result.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Scalar subsets containing the new global root. -/
def RootedGluedSet :=
  {W : Set (Option CoordNode) // none ∈ W}

namespace TypedVectorSubset

/-- Read a glued scalar set back as its three typed coordinate slices. -/
def ofGlued (W : Set (Option CoordNode)) : TypedVectorSubset where
  carrier i := {x | sort x = i ∧ some x ∈ W}
  correctlyTyped := by
    intro i x hx
    exact hx.1

theorem ofGlued_mem_iff
    (W : Set (Option CoordNode)) (i : Fin 3)
    (x : CoordNode) :
    x ∈ (ofGlued W).carrier i ↔
      sort x = i ∧ some x ∈ W := Iff.rfl

/-- Recover the original scalar set exactly provided it contains
the added root (as every root-anchored strong subtree does). -/
theorem glue_ofGlued
    (W : Set (Option CoordNode)) (hroot : none ∈ W) :
    (ofGlued W).glue = W := by
  ext q
  cases q with
  | none =>
      constructor
      · intro _
        exact hroot
      · intro _
        exact (ofGlued W).root_mem
  | some x =>
      rw [some_mem_iff]
      change (sort x = sort x ∧ some x ∈ W) ↔ some x ∈ W
      simp

theorem ofGlued_glue
    (V : TypedVectorSubset) :
    ofGlued V.glue = V := by
  apply glue_injective
  exact glue_ofGlued V.glue V.root_mem

/-- Exact equivalence between typed vector subsets and root-containing
scalar subsets of the glued ambient tree. -/
def equivRootedGluedSet : TypedVectorSubset ≃ RootedGluedSet where
  toFun V := ⟨V.glue, V.root_mem⟩
  invFun W := ofGlued W.val
  left_inv V := ofGlued_glue V
  right_inv W := by
    apply Subtype.ext
    exact glue_ofGlued W.val W.property

end TypedVectorSubset
end CoordNode
end ThreeUniformDiaries
