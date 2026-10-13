import ThreeUniformDiaries.FiniteBranchMapPrefixInvariance
import ThreeUniformDiaries.FiniteInfiniteBranchExact
import ThreeUniformDiaries.ScalarFiniteCanonicalBranchDecoder
import ThreeUniformDiaries.RootGluedVectorRefinement

/-!
# Exact agreement: choice-free finite scalar F_I decoder = infinite F_I

Take a genuine synchronized E0/E1/E2 infinite strong picture and glue
it into the literal arbitrary-branching scalar Milliken strong tree X.
There are TWO independent definitions of its selected finite branch map:

* decode the finite approximation r_(k+2)(X) using its unique
  realization-independent typed carrier and *canonical* height map;
* use the actual infinite geometric canonical map F_X on K_empty.

We prove they agree as WHOLE dependent EnumerationBranchNode records,
for every source vertex of last index <= k.

The key input is finite E2/E1/E0 recursion invariance under changing
the unused selected levels above k, together with the earlier full
finite/infinite branch equality on genuine coordinate prefixes.

This eliminates the final ambiguity between an actual geometric
refinement and the scalar finite code on which Milliken colours.
There is no heterogeneous HL hypothesis in this equality.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree
open ThreeUniformDiaries.CoordNode

/-- The intrinsic finite decoder of the scalar tree induced by a true
three-coordinate infinite strong vector agrees exactly with the
infinite canonical F_I branch action. -/
theorem rootedScalarFiniteBranchMap_eq_infiniteCanonical
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f) (k : Nat)
    (B : EnumerationBranchNode) (hB : B.last ≤ k)
    (hroot : (none : WithBot CoordNode) ∈
      (r (k + 2) (gluedVectorStrong_to_milliken h₀ h₁ h₂ hf)).carrier) :
    rootedScalarFiniteBranchMap k
      (r (k + 2) (gluedVectorStrong_to_milliken h₀ h₁ h₂ hf))
      hroot B hB =
      (infiniteStrongPictureCanonicalMap h₀ h₁ h₂ hf).mapBranch B := by
  let X := gluedVectorStrong_to_milliken h₀ h₁ h₂ hf
  let a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2) :=
    r (k + 2) X
  let V := typedVectorOfStrong h₀ h₁ h₂
  let C := chooseFinitePictures k a hroot
  let g := canonicalFiniteLevelMap k a
  have hprefix : a.carrier = (V.truncateSelected f (k + 1)).glue := by
    change X.initialPart (k + 2) =
      (V.truncateSelected f (k + 1)).glue
    simpa only [Nat.add_assoc, Nat.reduceAdd, X, V] using
      (gluedVectorStrong_initialPart_eq_vectorPrefix
        h₀ h₁ h₂ hf (k + 1))
  have hcarrier :
      finiteTypedCarrier k a = V.truncateSelected f (k + 1) := by
    change TypedVectorSubset.ofGlued a.carrier = _
    rw [hprefix]
    exact TypedVectorSubset.ofGlued_glue _
  obtain ⟨hF₀, hF₁, hF₂⟩ :=
    typedVectorStrong_finiteSlice_eq h₀ h₁ h₂ hf k
  have hS₀ :
      infiniteStrongPicture_finitePrefix S₀ f k =
        (finiteTypedCarrier k a).carrier 0 := by
    rw [hcarrier]
    exact hF₀.symm
  have hS₁ :
      infiniteStrongPicture_finitePrefix S₁ f k =
        (finiteTypedCarrier k a).carrier 1 := by
    rw [hcarrier]
    exact hF₁.symm
  have hS₂ :
      infiniteStrongPicture_finitePrefix S₂ f k =
        (finiteTypedCarrier k a).carrier 2 := by
    rw [hcarrier]
    exact hF₂.symm
  have hheight : ∀ i : Nat, i ≤ k → f i = g i := by
    intro i hi
    have hreal :
        g i = CoordNode.millikenCoordinateLevels X i :=
      canonicalFiniteLevelMap_eq_realizer k a X rfl i hi
    have hnorm : CoordNode.millikenCoordinateLevels X i = f i := by
      change gluedSelectedLevel f (i + 1) - 1 = f i
      rw [gluedSelectedLevel_succ]
      omega
    exact hnorm.symm.trans hreal.symm
  have hcode :
      finiteStrongPicture_branchMap
        (infiniteStrongPicture_finitePrefix_strong h₀ hf rfl k)
        (infiniteStrongPicture_finitePrefix_strong h₁ hf rfl k)
        (infiniteStrongPicture_finitePrefix_strong h₂ hf rfl k)
        B hB =
      finiteStrongPicture_branchMap C.h₀ C.h₁ C.h₂ B hB :=
    finiteStrongPicture_branchMap_eq_of_equal_carriers_and_heights
      (infiniteStrongPicture_finitePrefix_strong h₀ hf rfl k)
      (infiniteStrongPicture_finitePrefix_strong h₁ hf rfl k)
      (infiniteStrongPicture_finitePrefix_strong h₂ hf rfl k)
      C.h₀ C.h₁ C.h₂ hS₀ hS₁ hS₂ hheight B hB
  have hcoh :=
    finitePrefix_branchMap_eq_infinite h₀ h₁ h₂ hf k B hB
  change finiteStrongPicture_branchMap C.h₀ C.h₁ C.h₂ B hB =
    (infiniteStrongPictureCanonicalMap h₀ h₁ h₂ hf).mapBranch B
  exact hcode.symm.trans hcoh

end ATRFiniteDecoder
end ThreeUniformDiaries
