import ThreeUniformDiaries.ScalarGeometricBranchRefinement
import ThreeUniformDiaries.ScalarCompleteInitialStem
import ThreeUniformDiaries.CanonicalRelativeFixedLevels

/-!
# The protected scalar ATR refinement has the exact K_I composition action

Starting with two actual E0/E1/E2 strong triples, with initial
coordinate source levels fixed through n-1, the checked geometric
canonical-map composition produces a composite strong triple.

We prove all three properties required in the final Ramsey
application simultaneously:

* its root-glued scalar strong tree is a literal refinement of U;
* the first n+1 scalar Milliken source levels remain the full
  identity stem, not just n named vertices on the generic branch;
* the canonical F_I action on the COMPLETE relative K_I carrier
  equals the pointwise composition of the two original actions.

Thus no abstract "geometric refine_spec" or "protected root"
axiom is needed. The remaining finite-height task is to construct
an image code inside this refinement and match the independent
finite Option decoder to this canonical composition.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree
open ThreeUniformDiaries.CoordNode

theorem exists_protected_scalar_refinement_relativeBranch_comp
    {S₀ S₁ S₂ U₀ U₁ U₂ : Set CoordNode} {sigma f : Nat → Nat}
    {rS₀ : EnumNode (sigma 0)} {rS₁ : OneNode (sigma 0)}
    {rS₂ : AuxNode (sigma 0)}
    {rU₀ : EnumNode (f 0)} {rU₁ : OneNode (f 0)}
    {rU₂ : AuxNode (f 0)}
    (hS₀ : InfiniteStrongPicture S₀ sigma (.enum (sigma 0) rS₀))
    (hS₁ : InfiniteStrongPicture S₁ sigma (.one (sigma 0) rS₁))
    (hS₂ : InfiniteStrongPicture S₂ sigma (.aux (sigma 0) rS₂))
    (hU₀ : InfiniteStrongPicture U₀ f (.enum (f 0) rU₀))
    (hU₁ : InfiniteStrongPicture U₁ f (.one (f 0) rU₁))
    (hU₂ : InfiniteStrongPicture U₂ f (.aux (f 0) rU₂))
    (hsigma : StrictMono sigma) (hf : StrictMono f)
    (n : Nat) (I : EnumNode n)
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
        ∀ b : RelativeBranchNode I,
          (infiniteStrongPictureCanonicalMap
            hV₀ hV₁ hV₂ (hf.comp hsigma)).relativeMapBranch_of_fixed_levels
              I (by
                intro j hj
                change f (sigma j) = j
                rw [hfixS j hj, hfixU j hj]) b =
          (infiniteStrongPictureCanonicalMap
            hU₀ hU₁ hU₂ hf).relativeMapBranch_of_fixed_levels
              I hfixU
                ((infiniteStrongPictureCanonicalMap
                  hS₀ hS₁ hS₂ hsigma).relativeMapBranch_of_fixed_levels
                  I hfixS b) := by
  obtain ⟨V₂, V₁, V₀, hV₂, hV₁, hV₀, hRefines, hComp⟩ :=
    exists_scalar_geometric_refinement_with_branch_composition
      hS₀ hS₁ hS₂ hU₀ hU₁ hU₂ hsigma hf
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
  intro b
  apply Subtype.ext
  change (infiniteStrongPictureCanonicalMap
      hV₀ hV₁ hV₂ (hf.comp hsigma)).mapBranch b.val =
    (infiniteStrongPictureCanonicalMap hU₀ hU₁ hU₂ hf).mapBranch
      ((infiniteStrongPictureCanonicalMap
        hS₀ hS₁ hS₂ hsigma).mapBranch b.val)
  exact hComp b.val

end ATRFiniteDecoder
end ThreeUniformDiaries
