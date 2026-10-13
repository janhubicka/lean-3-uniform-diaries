import ThreeUniformDiaries.ScalarFinitePostcompositionRealization
import ThreeUniformDiaries.FiniteImageExactBranchMap
import ThreeUniformDiaries.FiniteInfiniteBranchExact

/-!
# Every real finite embedding has a protected scalar F_I realization

The outer generic self-embedding u is fixed BEFORE the finite source
embedding e is selected. Its pointwise action is the one fixed uniform
K_I embedding phi after the actual infinite canonical map F_U.

For an arbitrary genuine finite aux embedding e of A into G,
the verified finite Aemb converse produces a finite strong vector S
with F_S(g_A(i)) = g_G(e(i)) at every real source vertex.
The verified protected geometric composition produces X ≤ U with
the first n+1 scalar levels unchanged and with F_X = F_U ∘ F_S
on the first m source branch vertices.

Finally the full finite/infinite branch identity identifies the
finite canonical F_X code with the genuine infinite canonical map
of the *same* X. Thus X realizes exactly the postcomposed finite
image u∘e, with no hypothesis postulating a finite encoding or a
refinement-realisation law.

Only a separate identification of this canonical map with the
choice-independent finite scalar decoder is needed before applying
the already checked finite-colouring theorem to the witness u.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree
open ThreeUniformDiaries.CoordNode

/-- Uniformly in every real finite m=k+1 vertex embedding e fixing
the first n vertices, a single chosen outer self-embedding u has a
protected scalar strong refinement X whose GENUINE infinite canonical
branch map on the source A is literally phi⁻¹(u∘e), as an equality
of actual relative K_I branch vertices. -/
theorem exists_refinement_realizing_any_actual_finite_image
    (G : GenericEnumerated3Graph)
    {n k : Nat} (I : EnumNode n)
    (hI : G.graph.initialSegment n = I)
    (hnk : n ≤ k + 1)
    (E : SizeFirstBranchPresentation I)
    (phi : Nat → Nat)
    (hphi : UniversalAuxBranchProperty G I E phi)
    {U₀ U₁ U₂ : Set CoordNode} {f : Nat → Nat}
    {rU₀ : EnumNode (f 0)}
    {rU₁ : OneNode (f 0)}
    {rU₂ : AuxNode (f 0)}
    (hU₀ : InfiniteStrongPicture U₀ f (.enum (f 0) rU₀))
    (hU₁ : InfiniteStrongPicture U₁ f (.one (f 0) rU₁))
    (hU₂ : InfiniteStrongPicture U₂ f (.aux (f 0) rU₂))
    (hf : StrictMono f)
    (hfixU : ∀ j < n, f j = j)
    (u : Ordered3Graph.Embedding G.graph G.graph)
    (hvalue : ∀ j : Nat,
      ∃ hB : InRelativeBranchGraph I
        ((infiniteStrongPictureCanonicalMap hU₀ hU₁ hU₂ hf).mapBranch
          (G.graph.branchNode j)),
        u j = phi (E.code.symm
          (⟨(infiniteStrongPictureCanonicalMap hU₀ hU₁ hU₂ hf).mapBranch
              (G.graph.branchNode j), hB⟩ : RelativeBranchNode I)))
    (A : EnumNode (k + 1))
    (e : Ordered3Graph.FiniteAuxEmbeddingImage
      A.toOrdered3Graph G.graph (k + 1))
    (hfixe : ∀ i : Fin (k + 1), i.val < n → e.image i = i.val) :
    ∃ X : StrongSubtree CoordNode.rootGluedAmbientTree,
      X.Refines (gluedVectorStrong_to_milliken hU₀ hU₁ hU₂ hf) ∧
      r (n + 1) X =
        r (n + 1) (gluedVectorStrong_to_milliken hU₀ hU₁ hU₂ hf) ∧
      ∃ F : CanonicalMap,
        F.level = CoordNode.millikenCoordinateLevels X ∧
        ∀ i : Fin (k + 1),
          ∃ hB : InRelativeBranchGraph I
            (F.mapBranch (A.toOrdered3Graph.branchNode i.val)),
            u (e.image i) = phi (E.code.symm
              (⟨F.mapBranch (A.toOrdered3Graph.branchNode i.val), hB⟩ :
                RelativeBranchNode I)) := by
  obtain ⟨sigma, hsigma, hfixS, rS₀, rS₁, rS₂,
      S₀, S₁, S₂, hS₀, hS₁, hS₂, hCode⟩ :=
    A.exists_finiteImage_exact_branchMap G.graph I hI
      (by omega) hnk e hfixe
  obtain ⟨V₂, V₁, V₀, hV₂, hV₁, hV₀,
      hRef, hStem, hFormula⟩ :=
    exists_protected_scalar_refinement_postcompose_with_fixed_embedding
      G I hI E phi hphi A
      hS₀ hS₁ hS₂ hU₀ hU₁ hU₂
      hsigma hf hfixS hfixU u hvalue e hCode
  let X : StrongSubtree CoordNode.rootGluedAmbientTree :=
    gluedVectorStrong_to_milliken hV₀ hV₁ hV₂ (hf.comp hsigma)
  let F : CanonicalMap :=
    infiniteStrongPictureCanonicalMap hV₀ hV₁ hV₂ (hf.comp hsigma)
  have hlevel : F.level = CoordNode.millikenCoordinateLevels X := by
    funext j
    change f (sigma j) =
      X.levels (j + 1) - 1
    change f (sigma j) =
      gluedSelectedLevel (fun i => f (sigma i)) (j + 1) - 1
    rw [gluedSelectedLevel_succ]
    omega
  refine ⟨X, hRef, hStem, F, hlevel, ?_⟩
  intro i
  let B : EnumerationBranchNode :=
    A.toOrdered3Graph.branchNode i.val
  have hBLe : B.last ≤ k := Nat.le_of_lt_succ i.isLt
  let C : EnumerationBranchNode :=
    finiteStrongPicture_branchMap
      (infiniteStrongPicture_finitePrefix_strong
        hV₀ (hf.comp hsigma) rfl k)
      (infiniteStrongPicture_finitePrefix_strong
        hV₁ (hf.comp hsigma) rfl k)
      (infiniteStrongPicture_finitePrefix_strong
        hV₂ (hf.comp hsigma) rfl k) B hBLe
  obtain ⟨hC, hValue⟩ := hFormula i
  have hEq : C = F.mapBranch B :=
    finitePrefix_branchMap_eq_infinite
      hV₀ hV₁ hV₂ (hf.comp hsigma) k B hBLe
  have hRel : InRelativeBranchGraph I (F.mapBranch B) := by
    rw [← hEq]
    exact hC
  refine ⟨hRel, ?_⟩
  have hSubtype :
      (⟨C, hC⟩ : RelativeBranchNode I) =
      (⟨F.mapBranch B, hRel⟩ : RelativeBranchNode I) := by
    apply Subtype.ext
    exact hEq
  change u (e.image i) =
    phi (E.code.symm
      (⟨F.mapBranch B, hRel⟩ : RelativeBranchNode I))
  calc
    u (e.image i) =
        phi (E.code.symm (⟨C, hC⟩ : RelativeBranchNode I)) :=
      hValue
    _ = phi (E.code.symm
        (⟨F.mapBranch B, hRel⟩ : RelativeBranchNode I)) :=
      congrArg (fun z : RelativeBranchNode I =>
        phi (E.code.symm z)) hSubtype

end ATRFiniteDecoder
end ThreeUniformDiaries
