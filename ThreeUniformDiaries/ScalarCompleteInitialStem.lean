import ThreeUniformDiaries.RootGluedVectorRefinement
import ThreeUniformDiaries.InfiniteStrongCompleteFixedPrefix
import ThreeUniformDiaries.ScalarAnchoredInitialTypes
import Milliken.GeneralTree.Identity

/-!
# Complete initial coordinate type levels give the exact scalar identity stem

The Ramsey application needs the first n+1 scalar Milliken source
levels protected, which is stronger than fixing the first n vertices
along one enumeration branch.

A synchronized genuine E0/E1/E2 strong triple whose selected
coordinate levels f(j) are literally j for j<n automatically fills
ALL actual type nodes on those initial levels; this follows from the
verified concrete canonical maps. Root-gluing therefore gives exactly
the first n+1 source levels of the *identity* ambient scalar tree.

The equivalence of the entire initial scalar finite approximations
is proved by node-carrier extensionality and the exact rank shift,
without any homogenization or globally bounded branching alphabet.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree
open ThreeUniformDiaries.CoordNode

/-- Complete genuine ambient initial levels, together with selected
levels equal to their ambient indices, force equality of finite
Milliken approximations with the full identity strong tree. -/
theorem scalar_identityStem_of_complete_levels
    {U : Milliken.AmbientTree}
    (B : StrongSubtree U) (d : Nat)
    (hlevels : ∀ j : Nat, j < d → B.levels j = j)
    (hfull : ∀ x : U, U.level x < d → x ∈ B.carrier) :
    r d B = r d (identityStrongSubtree U) := by
  apply FiniteApprox.ext_carrier
  ext x
  constructor
  · rintro ⟨hx, j, hjd, hrank⟩
    refine ⟨Set.mem_univ _, j, hjd, ?_⟩
    change U.level x = j
    rw [← hlevels j hjd]
    exact hrank
  · rintro ⟨_, j, hjd, hrank⟩
    have hx : x ∈ B.carrier := hfull x (by
      change U.level x = j at hrank
      rw [hrank]
      exact hjd)
    refine ⟨hx, j, hjd, ?_⟩
    change U.level x = B.levels j
    rw [hlevels j hjd]
    exact hrank

/-- For the actual nonhomogeneous E0/E1/E2 root-glued type tree,
every synchronized strong vector with f(j)=j for j<n has
EXACTLY the protected scalar identity approximation of height n+1. -/
theorem gluedVectorStrong_identityStem
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    (n : Nat) (hfix : ∀ j < n, f j = j) :
    r (n + 1) (gluedVectorStrong_to_milliken h₀ h₁ h₂ hf) =
      r (n + 1) scalarIdentity := by
  let B := gluedVectorStrong_to_milliken h₀ h₁ h₂ hf
  have hAux :=
    infiniteAuxStrongPicture_completePrefix h₂ hf hfix
  have hOne :=
    infiniteOneStrongPicture_completePrefix h₁ h₂ hf hfix
  have hEnum :=
    infiniteEnumStrongPicture_completePrefix h₀ h₁ h₂ hf hfix
  have hlevels : ∀ j : Nat, j < n + 1 → B.levels j = j := by
    intro j hj
    cases j with
    | zero => rfl
    | succ i =>
        have hi : i < n := by omega
        change f i + 1 = i + 1
        rw [hfix i hi]
  have hfull :
      ∀ x : CoordNode.rootGluedAmbientTree,
        CoordNode.rootGluedAmbientTree.level x < n + 1 →
          x ∈ B.carrier := by
    intro x hx
    cases x with
    | none =>
        change (none : WithBot CoordNode) ∈
          gluedVectorStrongCarrier h₀ h₁ h₂
        exact gluedVectorStrongCarrier_root_mem h₀ h₁ h₂
    | some x =>
        have hxN : level x < n := by
          have hrank := rootGluedAmbient_level_coe x
          change rootGluedAmbientTree.level
            (x : WithBot CoordNode) < n + 1 at hx
          omega
        cases x with
        | aux j a =>
            change (some (CoordNode.aux j a) : WithBot CoordNode) ∈
              gluedVectorStrongCarrier h₀ h₁ h₂
            exact (gluedVectorStrongCarrier_aux_iff
              h₀ h₁ h₂ j a).mpr (hAux j hxN a)
        | one j a =>
            change (some (CoordNode.one j a) : WithBot CoordNode) ∈
              gluedVectorStrongCarrier h₀ h₁ h₂
            exact (gluedVectorStrongCarrier_one_iff
              h₀ h₁ h₂ j a).mpr (hOne j hxN a)
        | enum j a =>
            change (some (CoordNode.enum j a) : WithBot CoordNode) ∈
              gluedVectorStrongCarrier h₀ h₁ h₂
            exact (gluedVectorStrongCarrier_enum_iff
              h₀ h₁ h₂ j a).mpr (hEnum j hxN a)
  change r (n + 1) B =
    r (n + 1) (identityStrongSubtree rootGluedAmbientTree)
  exact scalar_identityStem_of_complete_levels B (n + 1)
    hlevels hfull

end ATRFiniteDecoder
end ThreeUniformDiaries
