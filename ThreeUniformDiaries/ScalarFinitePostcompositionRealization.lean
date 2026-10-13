import ThreeUniformDiaries.ScalarUniformGenericSelfEmbedding
import ThreeUniformDiaries.FiniteImageAembCoding
import ThreeUniformDiaries.ScalarFiniteRefinementRealization
import ThreeUniformDiaries.FiniteAuxEmbeddingPostcomposition

/-!
# The postcomposed finite A-embedding equals the actual realised scalar F_I code

This is the missing mathematical equality in the concluding Ramsey
argument, before the finite scalar colour is evaluated.

Take a genuine finite strong three-coordinate picture S whose F_I
branch action encodes the m actual images of a source finite embedding
e : A -> G. Take a genuine infinite strong picture U with the full
initial n-coordinate levels fixed. The verified finite-to-infinite
geometric composition constructs a scalar strong refinement X of U,
protecting the first n+1 scalar levels and satisfying F_X = F_U ∘ F_S
on every finite branch vertex.

Simultaneously, the independently proved uniform K_I embedding produces
the actual ambient self-embedding u = phi ∘ F_U ∘ g_G.
We check, for EVERY genuine source vertex i, that the finite F_X
branch code produces exactly u(e(i)) after applying the ONE fixed phi.
No synthetic FinCode realisation property or assumed composition
identity occurs, and there is no use of the unfinished heterogeneous
boundary-product HL statement.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree
open ThreeUniformDiaries.CoordNode

/-- Actual finite-image postcomposition and the finite F_I code of a
protected scalar strong refinement have identical values at each of
the m real source vertices.

The only coding premise here is the genuine finite Aemb branch
identity for the inner finite three-coordinate picture; that identity
is constructed for every finite aux embedding by
`EnumNode.exists_finiteImage_relativeBranch_coding`. -/
theorem exists_protected_scalar_refinement_postcompose_formula
    (G : GenericEnumerated3Graph)
    {n k : Nat} (I : EnumNode n)
    (hI : G.graph.initialSegment n = I)
    (E : SizeFirstBranchPresentation I)
    (phi : Nat → Nat)
    (hphi : UniversalAuxBranchProperty G I E phi)
    (A : EnumNode (k + 1))
    {S₀ S₁ S₂ U₀ U₁ U₂ : Set CoordNode}
    {sigma f : Nat → Nat}
    {rS₀ : EnumNode (sigma 0)}
    {rS₁ : OneNode (sigma 0)}
    {rS₂ : AuxNode (sigma 0)}
    {rU₀ : EnumNode (f 0)}
    {rU₁ : OneNode (f 0)}
    {rU₂ : AuxNode (f 0)}
    (hS₀ : FiniteStrongPicture S₀ sigma k
      (.enum (sigma 0) rS₀))
    (hS₁ : FiniteStrongPicture S₁ sigma k
      (.one (sigma 0) rS₁))
    (hS₂ : FiniteStrongPicture S₂ sigma k
      (.aux (sigma 0) rS₂))
    (hU₀ : InfiniteStrongPicture U₀ f (.enum (f 0) rU₀))
    (hU₁ : InfiniteStrongPicture U₁ f (.one (f 0) rU₁))
    (hU₂ : InfiniteStrongPicture U₂ f (.aux (f 0) rU₂))
    (hsigma : StrictMono sigma) (hf : StrictMono f)
    (hfixS : ∀ j < n, sigma j = j)
    (hfixU : ∀ j < n, f j = j)
    (e : Ordered3Graph.FiniteAuxEmbeddingImage
      A.toOrdered3Graph G.graph (k + 1))
    (hCode : ∀ i : Fin (k + 1),
      finiteStrongPicture_branchMap hS₀ hS₁ hS₂
        (A.toOrdered3Graph.branchNode i.val)
        (Nat.le_of_lt_succ i.isLt) =
        G.graph.branchNode (e.image i)) :
    ∃ u : Ordered3Graph.Embedding G.graph G.graph,
      u.AuxTypeRespecting ∧
      (∀ j < n, u j = j) ∧
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
        ∀ i : Fin (k + 1),
          ∃ hB : InRelativeBranchGraph I
            (finiteStrongPicture_branchMap
              (infiniteStrongPicture_finitePrefix_strong
                hV₀ (hf.comp hsigma) rfl k)
              (infiniteStrongPicture_finitePrefix_strong
                hV₁ (hf.comp hsigma) rfl k)
              (infiniteStrongPicture_finitePrefix_strong
                hV₂ (hf.comp hsigma) rfl k)
              (A.toOrdered3Graph.branchNode i.val)
              (Nat.le_of_lt_succ i.isLt)),
            u (e.image i) = phi (E.code.symm
              (⟨finiteStrongPicture_branchMap
                  (infiniteStrongPicture_finitePrefix_strong
                    hV₀ (hf.comp hsigma) rfl k)
                  (infiniteStrongPicture_finitePrefix_strong
                    hV₁ (hf.comp hsigma) rfl k)
                  (infiniteStrongPicture_finitePrefix_strong
                    hV₂ (hf.comp hsigma) rfl k)
                  (A.toOrdered3Graph.branchNode i.val)
                  (Nat.le_of_lt_succ i.isLt), hB⟩ :
                RelativeBranchNode I)) := by
  obtain ⟨u, haux, hfix, hvalue⟩ :=
    exists_uniform_canonical_selfEmbedding_of_vector
      G I hI E phi hphi hU₀ hU₁ hU₂ hf hfixU
  obtain ⟨V₂, V₁, V₀, hV₂, hV₁, hV₀,
      hRef, hStem, hComp⟩ :=
    exists_protected_scalar_refinement_realizing_finite_branch
      hS₀ hS₁ hS₂ hU₀ hU₁ hU₂
      hsigma hf n hfixS hfixU
  refine ⟨u, haux, hfix, V₂, V₁, V₀,
    hV₂, hV₁, hV₀, hRef, hStem, ?_⟩
  intro i
  let b : EnumerationBranchNode :=
    A.toOrdered3Graph.branchNode i.val
  have hb : b.last ≤ k := Nat.le_of_lt_succ i.isLt
  let d : EnumerationBranchNode :=
    finiteStrongPicture_branchMap
      (infiniteStrongPicture_finitePrefix_strong
        hV₀ (hf.comp hsigma) rfl k)
      (infiniteStrongPicture_finitePrefix_strong
        hV₁ (hf.comp hsigma) rfl k)
      (infiniteStrongPicture_finitePrefix_strong
        hV₂ (hf.comp hsigma) rfl k) b hb
  have hd :
      d =
        (infiniteStrongPictureCanonicalMap hU₀ hU₁ hU₂ hf).mapBranch
          (G.graph.branchNode (e.image i)) := by
    calc
      d = (infiniteStrongPictureCanonicalMap
            hU₀ hU₁ hU₂ hf).mapBranch
              (finiteStrongPicture_branchMap hS₀ hS₁ hS₂ b hb) :=
        hComp b hb
      _ = (infiniteStrongPictureCanonicalMap
            hU₀ hU₁ hU₂ hf).mapBranch
              (G.graph.branchNode (e.image i)) := by
        rw [hCode i]
  obtain ⟨hBI, hu⟩ := hvalue (e.image i)
  have hBd : InRelativeBranchGraph I d := by
    rw [hd]
    exact hBI
  refine ⟨hBd, ?_⟩
  have hsub :
      (⟨(infiniteStrongPictureCanonicalMap hU₀ hU₁ hU₂ hf).mapBranch
        (G.graph.branchNode (e.image i)), hBI⟩ : RelativeBranchNode I) =
      (⟨d, hBd⟩ : RelativeBranchNode I) := by
    apply Subtype.ext
    exact hd.symm
  change u (e.image i) = phi (E.code.symm
    (⟨d, hBd⟩ : RelativeBranchNode I))
  calc
    u (e.image i) =
        phi (E.code.symm
          (⟨(infiniteStrongPictureCanonicalMap hU₀ hU₁ hU₂ hf).mapBranch
              (G.graph.branchNode (e.image i)), hBI⟩ :
            RelativeBranchNode I)) := hu
    _ = phi (E.code.symm (⟨d, hBd⟩ : RelativeBranchNode I)) :=
      congrArg (fun z : RelativeBranchNode I => phi (E.code.symm z)) hsub

end ATRFiniteDecoder
end ThreeUniformDiaries
