import ThreeUniformDiaries.ScalarAnchoredInitialTypes
import ThreeUniformDiaries.RootGluedFixedLevelDecoder
import ThreeUniformDiaries.FiniteInfiniteBranchCoherence

/-!
# A scalar ATR finite-code shape independent of its infinite realizer

The colour passed to Milliken must be defined on genuine finite
approximations, whose witness of realization by an infinite strong
tree is proof-irrelevant. We therefore obtain the *finite* coordinate
heights from an arbitrary realizer and prove that every other realizer
gives exactly the same values, using the previously verified rigidity
of selected source levels.

The typed finite carrier is read directly from the finite approximation,
and hence needs no choice. Every approximation containing the added
scalar root gives three genuine finite strong type-tree pictures with
these exact finite heights. None of this assumes heterogeneous HL
or postulates a canonical finite-code decoder.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree
open ThreeUniformDiaries.CoordNode

/-- The intrinsic three-coordinate carrier of a finite scalar
approximation, determined *only* by its node set. -/
def finiteTypedCarrier (k : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2)) :
    CoordNode.TypedVectorSubset :=
  CoordNode.TypedVectorSubset.ofGlued a.carrier

/-- A canonical enumeration of the finite selected coordinate levels
of a genuine scalar approximation. The choice is shown irrelevant. -/
noncomputable def finiteCoordinateHeights (k : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2)) :
    Fin (k + 1) → Nat :=
  fun i =>
    CoordNode.millikenCoordinateLevels
      (Classical.choose a.realised) i.val

/-- The first k+1 coordinate levels of any realizer are exactly
the intrinsic finite heights of the finite approximation. -/
theorem finiteCoordinateHeights_eq_realizer
    (k : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (S : StrongSubtree CoordNode.rootGluedAmbientTree)
    (hS : a.carrier = S.initialPart (k + 2))
    (i : Fin (k + 1)) :
    finiteCoordinateHeights k a i =
      CoordNode.millikenCoordinateLevels S i.val := by
  let T : StrongSubtree CoordNode.rootGluedAmbientTree :=
    Classical.choose a.realised
  have hT : a.carrier = T.initialPart (k + 2) :=
    Classical.choose_spec a.realised
  have hEq : T.initialPart (k + 2) = S.initialPart (k + 2) :=
    hT.symm.trans hS
  have hi : i.val + 1 < k + 2 := by
    have hlt := i.isLt
    omega
  have hlevel := sourceLevels_eq_of_initialPart_eq
    T S (k + 2) hEq (i.val + 1) hi
  change T.levels (i.val + 1) - 1 =
    S.levels (i.val + 1) - 1
  exact congrArg (fun m : Nat => m - 1) hlevel

/-- In particular, equal genuine finite approximations have
identical intrinsic typed carriers and selected coordinate heights. -/
theorem finiteCode_eq_of_approx_eq
    (k : Nat)
    (a b : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (hab : a = b) :
    finiteTypedCarrier k a = finiteTypedCarrier k b ∧
      finiteCoordinateHeights k a = finiteCoordinateHeights k b := by
  subst b
  exact ⟨rfl, rfl⟩

/-- Every scalar finite approximation containing the true added root
is realizable as synchronized genuine finite E0/E1/E2 strong pictures,
using *exactly* its intrinsic finite height map. -/
theorem finiteCode_has_genuine_pictures
    (k : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (hroot : (none : WithBot CoordNode) ∈ a.carrier) :
    ∃ (f : Nat → Nat),
      StrictMono f ∧
      (∀ i : Fin (k + 1), finiteCoordinateHeights k a i = f i.val) ∧
      ∃ (r₀ : EnumNode (f 0))
        (r₁ : OneNode (f 0))
        (r₂ : AuxNode (f 0)),
          FiniteStrongPicture (finiteTypedCarrier k a).carrier 0
            f k (.enum (f 0) r₀) ∧
          FiniteStrongPicture (finiteTypedCarrier k a).carrier 1
            f k (.one (f 0) r₁) ∧
          FiniteStrongPicture (finiteTypedCarrier k a).carrier 2
            f k (.aux (f 0) r₂) := by
  let S : StrongSubtree CoordNode.rootGluedAmbientTree :=
    Classical.choose a.realised
  have hS : a.carrier = S.initialPart (k + 2) :=
    Classical.choose_spec a.realised
  have hmem : (none : WithBot CoordNode) ∈ S.carrier :=
    (hS ▸ hroot).1
  have hSroot : S.root = (none : WithBot CoordNode) := by
    apply le_antisymm
    · exact S.root_below _ hmem
    · exact bot_le
  obtain ⟨F, r₀, r₁, r₂, hf, h₀, h₁, h₂, hF⟩ :=
    CoordNode.millikenStrong_exists_fixedlevel_finite_vector S hSroot k
  let f := CoordNode.millikenCoordinateLevels S
  have hCarrier : a.carrier = F.glue := hS.trans hF
  have hFCode : F = finiteTypedCarrier k a := by
    have hrecover :=
      CoordNode.TypedVectorSubset.ofGlued_glue F
    change CoordNode.TypedVectorSubset.ofGlued F.glue = F at hrecover
    have hEq : finiteTypedCarrier k a = F := by
      change CoordNode.TypedVectorSubset.ofGlued a.carrier = F
      rw [hCarrier]
      exact hrecover
    exact hEq.symm
  refine ⟨f, hf, ?_, r₀, r₁, r₂, ?_, ?_, ?_⟩
  · intro i
    exact finiteCoordinateHeights_eq_realizer k a S hS i
  · rw [← hFCode]
    exact h₀
  · rw [← hFCode]
    exact h₁
  · rw [← hFCode]
    exact h₂

/-- A total, non-computationally chosen scalar finite-code shape.
The absence of the true added root is represented by `none`.
On valid rooted finite approximations the shape is actual geometry,
not arbitrary data in place of a checked vector picture. -/
noncomputable def decodeFiniteShape
    (k : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2)) :
    Option (CoordNode.TypedVectorSubset × (Fin (k + 1) → Nat)) := by
  classical
  exact if (none : WithBot CoordNode) ∈ a.carrier then
    some (finiteTypedCarrier k a, finiteCoordinateHeights k a)
  else none

theorem decodeFiniteShape_of_root
    (k : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (hroot : (none : WithBot CoordNode) ∈ a.carrier) :
    decodeFiniteShape k a =
      some (finiteTypedCarrier k a, finiteCoordinateHeights k a) := by
  classical
  simp only [decodeFiniteShape, if_pos hroot]

end ATRFiniteDecoder
end ThreeUniformDiaries
