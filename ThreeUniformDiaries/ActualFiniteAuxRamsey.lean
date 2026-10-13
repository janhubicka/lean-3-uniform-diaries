import ThreeUniformDiaries.ScalarFiniteInfiniteFIEquality
import ThreeUniformDiaries.ActualFiniteImageScalarRefinement
import ThreeUniformDiaries.ScalarActualFiniteMillikenColour
import ThreeUniformDiaries.ScalarCompleteInitialStem
import Milliken.GeneralTree.Extensionality

/-!
# The finite aux-type Ramsey theorem from the exact scalar Milliken input

This completes the actual ATR application of heterogeneous Milliken.
The theorem colours genuine *finite* aux-type-respecting embeddings of
an enumerated 3-hypergraph A into the generic G, not zero-extended
maps on an artificial source tail.

The proof constructs the SINGLE uniform self-embedding u of G before
quantifying over finite embeddings e. Aemb codes e by a genuine finite
E0/E1/E2 strong vector; protected geometric composition realizes its
image u∘e by a scalar strong refinement X of the Milliken witness B.
The intrinsic scalar finite decoder of r_(m+1)(X) agrees with the
infinite F_X canonical map, on the entire dependent branch vertex
in K_I. Hence the independent finite-colour theorem gives one colour
for all u∘e.

No abstract AuxRamseyCoding realization axiom is used. The ONE
remaining non-geometric input is exactly
HasBoundaryProductHL rootGluedAmbientTree, explicit in the final type.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree
open ThreeUniformDiaries.CoordNode

/-- For the *fixed* outer self-embedding u=phi∘F_U∘g_G,
every genuine finite aux embedding e is represented by the
choice-independent scalar F_I colouring code of a protected
refinement X of the actual glued tree U. -/
theorem exists_refinement_realizing_actual_scalar_colour
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
    (hu : u.AuxTypeRespecting)
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
      ∃ hstem : r (n + 1) X = r (n + 1) scalarIdentity,
        ScalarFiniteImageEquation G A I E phi (r (k + 2) X)
          (protectedScalarApprox_root_mem k n
            (r (k + 2) X) ⟨X, rfl, hstem⟩)
          (e.postcompose u hu) := by
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
  have hUstem :
      r (n + 1) (gluedVectorStrong_to_milliken hU₀ hU₁ hU₂ hf) =
        r (n + 1) scalarIdentity :=
    gluedVectorStrong_identityStem hU₀ hU₁ hU₂ hf n hfixU
  have hXstem : r (n + 1) X = r (n + 1) scalarIdentity :=
    hStem.trans hUstem
  let hroot :
      (none : WithBot CoordNode) ∈ (r (k + 2) X).carrier :=
    protectedScalarApprox_root_mem k n (r (k + 2) X)
      ⟨X, rfl, hXstem⟩
  refine ⟨X, hRef, hXstem, ?_⟩
  intro i
  let B : EnumerationBranchNode :=
    A.toOrdered3Graph.branchNode i.val
  have hBle : B.last ≤ k := Nat.le_of_lt_succ i.isLt
  let D : EnumerationBranchNode :=
    finiteStrongPicture_branchMap
      (infiniteStrongPicture_finitePrefix_strong
        hV₀ (hf.comp hsigma) rfl k)
      (infiniteStrongPicture_finitePrefix_strong
        hV₁ (hf.comp hsigma) rfl k)
      (infiniteStrongPicture_finitePrefix_strong
        hV₂ (hf.comp hsigma) rfl k) B hBle
  obtain ⟨hDI, hval⟩ := hFormula i
  have hFinite :
      D =
        (infiniteStrongPictureCanonicalMap
          hV₀ hV₁ hV₂ (hf.comp hsigma)).mapBranch B :=
    finitePrefix_branchMap_eq_infinite
      hV₀ hV₁ hV₂ (hf.comp hsigma) k B hBle
  have hInfinite :
      rootedScalarFiniteBranchMap k (r (k + 2) X) hroot B hBle =
        (infiniteStrongPictureCanonicalMap
          hV₀ hV₁ hV₂ (hf.comp hsigma)).mapBranch B :=
    rootedScalarFiniteBranchMap_eq_infiniteCanonical
      hV₀ hV₁ hV₂ (hf.comp hsigma) k B hBle hroot
  have hDecoder :
      rootedScalarFiniteBranchMap k (r (k + 2) X) hroot B hBle = D :=
    hInfinite.trans hFinite.symm
  have hBI : InRelativeBranchGraph I
      (rootedScalarFiniteBranchMap k
        (r (k + 2) X) hroot B hBle) := by
    rw [hDecoder]
    exact hDI
  refine ⟨hBI, ?_⟩
  have hsub :
      (⟨D, hDI⟩ : RelativeBranchNode I) =
      (⟨rootedScalarFiniteBranchMap k
          (r (k + 2) X) hroot B hBle, hBI⟩ :
        RelativeBranchNode I) := by
    apply Subtype.ext
    exact hDecoder.symm
  calc
    (e.postcompose u hu).image i = u (e.image i) :=
      Ordered3Graph.FiniteAuxEmbeddingImage.postcompose_apply e u hu i
    _ = phi (E.code.symm (⟨D, hDI⟩ : RelativeBranchNode I)) := hval
    _ = phi (E.code.symm
          (⟨rootedScalarFiniteBranchMap k
            (r (k + 2) X) hroot B hBle, hBI⟩ :
              RelativeBranchNode I)) :=
      congrArg (fun z : RelativeBranchNode I =>
        phi (E.code.symm z)) hsub

/-- ACTUAL finite aux-type Ramsey theorem with the one remaining
heterogeneous scalar Halpern–Läuchli premise explicitly visible.
The postcomposition action is on the m=k+1 genuine finite images,
never on an arbitrary zero-extended source tail. -/
theorem actualFiniteAuxRamsey_of_boundaryProductHL
    (G : GenericEnumerated3Graph)
    {n k : Nat} (hnk : n ≤ k + 1)
    (A : EnumNode (k + 1))
    (I : EnumNode n)
    (hGI : G.graph.initialSegment n = I)
    (hAI : A.truncate n = I)
    (E : SizeFirstBranchPresentation I)
    (phi : Nat → Nat)
    (hphi : UniversalAuxBranchProperty G I E phi)
    (hHL : Milliken.GeneralTree.HasBoundaryProductHL
      CoordNode.rootGluedAmbientTree)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : Ordered3Graph.FiniteAuxEmbeddingImage
      A.toOrdered3Graph G.graph (k + 1) → κ) :
    ∃ (u : Ordered3Graph.Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
        (∀ j < n, u j = j) ∧
        ∃ color : κ,
          ∀ e : Ordered3Graph.FiniteAuxEmbeddingImage
              A.toOrdered3Graph G.graph (k + 1),
            (∀ i : Fin (k + 1), i.val < n → e.image i = i.val) →
            χ (e.postcompose u hu) = color := by
  obtain ⟨B, hBRef, hBstem, color, hMono⟩ :=
    actualScalarFiniteColour_monochromatic
      G hnk A I hAI E phi hphi hHL χ
  obtain ⟨hBroot, hBfix⟩ :=
    anchoredScalar_root_and_levels B n hBstem
  let f : Nat → Nat := CoordNode.millikenCoordinateLevels B
  have hf : StrictMono f :=
    CoordNode.millikenCoordinateLevels_strictMono B
      (CoordNode.millikenStrong_levels_zero_of_root B hBroot)
  obtain ⟨rU₀, rU₁, rU₂, hU₀, hU₁, hU₂⟩ :=
    CoordNode.millikenStrong_exists_actual_vector B hBroot
  let U : StrongSubtree CoordNode.rootGluedAmbientTree :=
    gluedVectorStrong_to_milliken hU₀ hU₁ hU₂ hf
  have hUB : U = B := by
    apply StrongSubtree.ext_carrier
    exact millikenStrong_recovered_vector_carrier
      B hBroot hU₀ hU₁ hU₂ hf
  obtain ⟨u, hu, hufix, hvalue⟩ :=
    exists_uniform_canonical_selfEmbedding_of_vector
      G I hGI E phi hphi hU₀ hU₁ hU₂ hf hBfix
  refine ⟨u, hu, hufix, color, ?_⟩
  intro e hfixe
  obtain ⟨X, hXU, hXstem, hXcode⟩ :=
    exists_refinement_realizing_actual_scalar_colour
      G I hGI hnk E phi hphi
      hU₀ hU₁ hU₂ hf hBfix u hu hvalue A e hfixe
  have hXB : X.Refines B := by
    rw [← hUB]
    exact hXU
  exact hMono X hXB hXstem (e.postcompose u hu) hXcode

end ATRFiniteDecoder
end ThreeUniformDiaries
