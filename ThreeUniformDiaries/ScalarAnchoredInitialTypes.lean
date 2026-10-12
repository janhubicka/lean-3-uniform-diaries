import ThreeUniformDiaries.ScalarApproxLevelRigidity
import ThreeUniformDiaries.RootGluedLevelNormalization
import Milliken.GeneralTree.Identity
import Milliken.GeneralTree.SourceLevels

/-!
# Anchored scalar Milliken stems protect the actual ATR initial types

If the first n+1 scalar selected source levels equal those of the
identity root-glued E0/E1/E2 ambient tree, then the chosen scalar root
is the additional root, the corresponding coordinate-level map fixes
j<n, and every type-tree node below those first n coordinate levels
belongs literally to the scalar strong subtree.

These are exactly the *geometric* fixed-prefix conditions needed by
the finite and infinite concrete relative K_I canonical-map APIs.
There is no artificial root selection or uniform branching bound.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree
open ThreeUniformDiaries.CoordNode

noncomputable def scalarIdentity :
    StrongSubtree CoordNode.rootGluedAmbientTree :=
  identityStrongSubtree CoordNode.rootGluedAmbientTree

/-- The anchored n+1 scalar approximation forces the genuine added
root and fixes the first n selected coordinate levels. -/
theorem anchoredScalar_root_and_levels
    (S : StrongSubtree CoordNode.rootGluedAmbientTree)
    (n : Nat)
    (hstem : r (n + 1) S = r (n + 1) scalarIdentity) :
    S.root = (none : WithBot CoordNode) ∧
      ∀ j : Nat, j < n →
        CoordNode.millikenCoordinateLevels S j = j := by
  have hlevel :
      ∀ j : Nat, j < n + 1 → S.levels j = j := by
    intro j hj
    have hh := sourceLevels_eq_of_approx_eq S scalarIdentity
      (n + 1) hstem j hj
    simpa only [scalarIdentity, identityStrongSubtree_levels] using hh
  have hroot : S.root = (none : WithBot CoordNode) :=
    CoordNode.millikenStrong_root_eq_gluedRoot S
      (hlevel 0 (Nat.zero_lt_succ n))
  refine ⟨hroot, ?_⟩
  intro j hj
  have hsucc : S.levels (j + 1) = j + 1 :=
    hlevel (j + 1) (Nat.succ_lt_succ hj)
  change S.levels (j + 1) - 1 = j
  omega

/-- Every actual E0/E1/E2 coordinate type node on one of the
protected initial coordinate heights is retained in the scalar tree. -/
theorem anchoredScalar_full_type_prefix
    (S : StrongSubtree CoordNode.rootGluedAmbientTree)
    (n : Nat)
    (hstem : r (n + 1) S = r (n + 1) scalarIdentity)
    (j : Nat) (hj : j < n)
    (x : CoordNode) (hx : CoordNode.level x = j) :
    (some x : WithBot CoordNode) ∈ S.carrier := by
  have hcarrier :
      S.initialPart (n + 1) =
        scalarIdentity.initialPart (n + 1) :=
    congrArg FiniteApprox.carrier hstem
  have hId :
      (some x : WithBot CoordNode) ∈
        scalarIdentity.initialPart (n + 1) := by
    refine ⟨Set.mem_univ _, j + 1, Nat.succ_lt_succ hj, ?_⟩
    change CoordNode.rootGluedAmbientTree.level
      (x : WithBot CoordNode) = j + 1
    rw [CoordNode.rootGluedAmbient_level_coe, hx]
  have hS :
      (some x : WithBot CoordNode) ∈ S.carrier := by
    have hPart : (some x : WithBot CoordNode) ∈
        S.initialPart (n + 1) := by
      rw [hcarrier]
      exact hId
    exact hPart.1
  exact hS

/-- The complete protected source prefix, stated uniformly for all
three genuine type-tree coordinates. -/
theorem anchoredScalar_full_initial_levels
    (S : StrongSubtree CoordNode.rootGluedAmbientTree)
    (n : Nat)
    (hstem : r (n + 1) S = r (n + 1) scalarIdentity) :
    ∀ (i : Fin 3) (j : Nat), j < n →
      ∀ x : CoordNode, CoordNode.sort x = i →
        CoordNode.level x = j →
        (some x : WithBot CoordNode) ∈ S.carrier := by
  intro i j hj x hs hx
  exact anchoredScalar_full_type_prefix S n hstem j hj x hx

end ATRFiniteDecoder
end ThreeUniformDiaries
