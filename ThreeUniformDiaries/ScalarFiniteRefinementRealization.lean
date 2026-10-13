import ThreeUniformDiaries.FiniteStrongBranchExtension
import ThreeUniformDiaries.ScalarProtectedGeometricComposition

/-!
# The actual finite-to-infinite F_I realization inside a Milliken refinement

This is the central application of genuine strong-tree geometry to the
ATR Ramsey theorem. Starting with an arbitrary synchronized finite
E0/E1/E2 strong code S and an infinite outer strong code U:

1. extend S to actual infinite strong pictures R with the *same* level map;
2. use genuine geometric composition R -> U to construct an infinite
   composite strong vector V entirely inside U;
3. prove its scalar root-gluing X refines the actual scalar U and
   preserves the whole protected n+1-level identity stem;
4. prove the actual FINITE F_I map of V's first k+1 coordinate
   source levels equals F_U applied to the finite F_I map of S.

All these equalities are on every branch of K_empty of last index at
most k, not only on a distinguished source copy. No synthetic FinCode
realization property is assumed, and the heterogeneous Milliken input
is nowhere used.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree
open ThreeUniformDiaries.CoordNode

/-- Actual strong-refinement realization of the finite canonical F_I
branch code, with the exact protected initial scalar Milliken stem.

The outputs are genuine infinite strong pictures, and the displayed
finite equality is about the actual first k+1 levels of those pictures.
This is the required geometric counterpart of the abstract
ATRScalarRealization.realize field. -/
theorem exists_protected_scalar_refinement_realizing_finite_branch
    {S₀ S₁ S₂ U₀ U₁ U₂ : Set CoordNode}
    {sigma f : Nat → Nat} {k : Nat}
    {rS₀ : EnumNode (sigma 0)}
    {rS₁ : OneNode (sigma 0)}
    {rS₂ : AuxNode (sigma 0)}
    {rU₀ : EnumNode (f 0)}
    {rU₁ : OneNode (f 0)}
    {rU₂ : AuxNode (f 0)}
    (hS₀ : FiniteStrongPicture S₀ sigma k (.enum (sigma 0) rS₀))
    (hS₁ : FiniteStrongPicture S₁ sigma k (.one (sigma 0) rS₁))
    (hS₂ : FiniteStrongPicture S₂ sigma k (.aux (sigma 0) rS₂))
    (hU₀ : InfiniteStrongPicture U₀ f (.enum (f 0) rU₀))
    (hU₁ : InfiniteStrongPicture U₁ f (.one (f 0) rU₁))
    (hU₂ : InfiniteStrongPicture U₂ f (.aux (f 0) rU₂))
    (hsigma : StrictMono sigma) (hf : StrictMono f)
    (n : Nat)
    (hfixS : ∀ j < n, sigma j = j)
    (hfixU : ∀ j < n, f j = j) :
    ∃ (V₂ V₁ V₀ : Set CoordNode),
      ∃ (hV₂ : InfiniteStrongPicture V₂ (fun i => f (sigma i))
        (.aux (f (sigma 0))
          (infiniteAuxCanonicalMap hU₂ (sigma 0) rS₂).val))
        (hV₁ : InfiniteStrongPicture V₁ (fun i => f (sigma i))
        (.one (f (sigma 0))
          (infiniteOneCanonicalMap hU₁ hU₂ (sigma 0) rS₁).val))
        (hV₀ : InfiniteStrongPicture V₀ (fun i => f (sigma i))
        (.enum (f (sigma 0))
          (infiniteEnumCanonicalMap hU₀ hU₁ hU₂ (sigma 0) rS₀).val)),
        (gluedVectorStrong_to_milliken hV₀ hV₁ hV₂
            (hf.comp hsigma)).Refines
          (gluedVectorStrong_to_milliken hU₀ hU₁ hU₂ hf) ∧
        r (n + 1)
            (gluedVectorStrong_to_milliken hV₀ hV₁ hV₂
              (hf.comp hsigma)) =
          r (n + 1)
            (gluedVectorStrong_to_milliken hU₀ hU₁ hU₂ hf) ∧
        ∀ B : EnumerationBranchNode, ∀ hB : B.last ≤ k,
          finiteStrongPicture_branchMap
              (infiniteStrongPicture_finitePrefix_strong
                hV₀ (hf.comp hsigma) rfl k)
              (infiniteStrongPicture_finitePrefix_strong
                hV₁ (hf.comp hsigma) rfl k)
              (infiniteStrongPicture_finitePrefix_strong
                hV₂ (hf.comp hsigma) rfl k)
              B hB =
            (infiniteStrongPictureCanonicalMap hU₀ hU₁ hU₂ hf).mapBranch
              (finiteStrongPicture_branchMap hS₀ hS₁ hS₂ B hB) := by
  obtain ⟨R₀, R₁, R₂, hR₀, hR₁, hR₂,
      hSR₀, hSR₁, hSR₂, hFinite⟩ :=
    exists_infinite_extension_with_branchMap_eq
      hS₀ hS₁ hS₂ hsigma
  obtain ⟨V₂, V₁, V₀, hV₂, hV₁, hV₀,
      hRefines, hComp⟩ :=
    exists_scalar_geometric_refinement_with_branch_composition
      hR₀ hR₁ hR₂ hU₀ hU₁ hU₂ hsigma hf
  have hfixV : ∀ j < n, f (sigma j) = j := by
    intro j hj
    rw [hfixS j hj, hfixU j hj]
  have hVStem :=
    gluedVectorStrong_identityStem hV₀ hV₁ hV₂
      (hf.comp hsigma) n hfixV
  have hUStem :=
    gluedVectorStrong_identityStem hU₀ hU₁ hU₂ hf n hfixU
  refine ⟨V₂, V₁, V₀, hV₂, hV₁, hV₀,
    hRefines, hVStem.trans hUStem.symm, ?_⟩
  intro B hB
  let F_U := infiniteStrongPictureCanonicalMap hU₀ hU₁ hU₂ hf
  let F_R := infiniteStrongPictureCanonicalMap hR₀ hR₁ hR₂ hsigma
  let F_V := infiniteStrongPictureCanonicalMap
    hV₀ hV₁ hV₂ (hf.comp hsigma)
  have hFV :
      finiteStrongPicture_branchMap
          (infiniteStrongPicture_finitePrefix_strong
            hV₀ (hf.comp hsigma) rfl k)
          (infiniteStrongPicture_finitePrefix_strong
            hV₁ (hf.comp hsigma) rfl k)
          (infiniteStrongPicture_finitePrefix_strong
            hV₂ (hf.comp hsigma) rfl k)
          B hB = F_V.mapBranch B := by
    exact finiteStrong_extension_branchMap_eq_infinite
      (infiniteStrongPicture_finitePrefix_strong
        hV₀ (hf.comp hsigma) rfl k)
      (infiniteStrongPicture_finitePrefix_strong
        hV₁ (hf.comp hsigma) rfl k)
      (infiniteStrongPicture_finitePrefix_strong
        hV₂ (hf.comp hsigma) rfl k)
      hV₀ hV₁ hV₂ (hf.comp hsigma)
      (fun _ hz => hz.1) (fun _ hz => hz.1) (fun _ hz => hz.1)
      B hB
  calc
    finiteStrongPicture_branchMap
        (infiniteStrongPicture_finitePrefix_strong
          hV₀ (hf.comp hsigma) rfl k)
        (infiniteStrongPicture_finitePrefix_strong
          hV₁ (hf.comp hsigma) rfl k)
        (infiniteStrongPicture_finitePrefix_strong
          hV₂ (hf.comp hsigma) rfl k)
        B hB = F_V.mapBranch B := hFV
    _ = F_U.mapBranch (F_R.mapBranch B) := hComp B
    _ = F_U.mapBranch (finiteStrongPicture_branchMap
          hS₀ hS₁ hS₂ B hB) := by rw [hFinite B hB]

end ATRFiniteDecoder
end ThreeUniformDiaries
