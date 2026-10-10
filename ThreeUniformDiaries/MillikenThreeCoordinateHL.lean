import Milliken.HalpernLauchli.HalesJewettBridge

/-!
# The verified synchronized three-coordinate Halpern-Läuchli input

The checked lean-milliken library proves the full finite-dimensional
strong-subtree Halpern–Läuchli theorem, not only the one-tree Milliken
theorem. In particular, for three homogeneous finitely-branching
coordinate trees and an arbitrary finite colouring of their level
products, it returns three strong embeddings with ONE common strictly
increasing level map.

This is a genuine synchronized vector input already available in
the dependency. The manuscript requires more: colours of finite
VECTOR STRONG SUBTREES (not merely level vectors), anchored first
ell levels, and the unbounded but finite level-dependent branching
of its T0 and T1 type trees. That transport still requires proof.
-/

namespace ThreeUniformDiaries

open Milliken

universe u

/-- The actual checked three-coordinate product HL theorem.
A single level map is supplied for all three strong subtrees. -/
theorem threeCoordinateStrongSubtreeHalpernLauchli
    {ι : Type u} [Finite ι] [Nonempty ι]
    (colors : Nat) [NeZero colors]
    (colour : (Fin 3 → Node ι) → Fin colors) :
    ∃ c : Fin colors,
      ∃ levels : Nat → Nat,
        ∃ F : Fin 3 → StrongEmbedding ι,
          HalpernLauchli.HasCommonLevels F levels ∧
          ∀ (n : Nat) (x : Fin 3 → Node ι),
            (∀ i, (x i).length = n) →
              colour (fun i => (F i).toFun (x i)) = c := by
  exact (HalpernLauchli.HalesJewettBridge.strongSubtreeHL ι)
    3 colors colour

end ThreeUniformDiaries
