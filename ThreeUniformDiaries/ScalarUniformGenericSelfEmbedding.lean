import ThreeUniformDiaries.ScalarAnchoredInitialTypes
import ThreeUniformDiaries.RootGluedReverseTriple
import ThreeUniformDiaries.InfiniteCanonicalRecord
import ThreeUniformDiaries.CanonicalInfiniteAuxEmbedding
import ThreeUniformDiaries.CanonicalInfiniteBranchFactorization
import ThreeUniformDiaries.CanonicalRelativeFixedLevels
import ThreeUniformDiaries.AuxTypeRespectingComposition
import ThreeUniformDiaries.UniversalAuxBranchEmbedding

/-!
# The genuine ambient self-embedding supplied by a scalar ATR tree

The final Ramsey witness has the manuscript's literal formula

  e = phi ∘ F_I^U ∘ g_G.

Here phi is the ONE uniform K_I embedding chosen in advance. From a
genuine synchronized infinite E0/E1/E2 strong picture U, the actual
canonical map F has a coherent induced image H of G and a genuine
aux-type-respecting embedding G -> H. The uniform branch property
supplies another aux embedding H -> G with the same phi. Their
composition is the required ambient self-embedding fixing n.

We prove its value at every source vertex is exactly the fixed phi
applied to the actual relative branch F_I(g_G(i)), not an abstractly
isomorphic embedding. We then obtain the result from an arbitrary
root-preserving scalar Milliken strong tree by the checked reverse
E0/E1/E2 extraction.

No heterogeneous Milliken theorem is needed to construct the witness.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree
open ThreeUniformDiaries.CoordNode

/-- Construct the actual fixed-prefix aux-type-respecting self-
embedding of the generic hypergraph from an infinite synchronized
E0/E1/E2 strong picture, using one preselected K_I embedding phi. -/
theorem exists_uniform_canonical_selfEmbedding_of_vector
    (G : GenericEnumerated3Graph)
    {n : Nat} (I : EnumNode n)
    (hI : G.graph.initialSegment n = I)
    (E : SizeFirstBranchPresentation I)
    (phi : Nat → Nat)
    (hphi : UniversalAuxBranchProperty G I E phi)
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    (hfix : ∀ j < n, f j = j) :
    ∃ e : Ordered3Graph.Embedding G.graph G.graph,
      e.AuxTypeRespecting ∧
      (∀ j : Nat, j < n → e j = j) ∧
      ∀ i : Nat,
        ∃ hB : InRelativeBranchGraph I
          ((infiniteStrongPictureCanonicalMap h₀ h₁ h₂ hf).mapBranch
            (G.graph.branchNode i)),
          e i = phi (E.code.symm
            (⟨(infiniteStrongPictureCanonicalMap h₀ h₁ h₂ hf).mapBranch
                (G.graph.branchNode i), hB⟩ : RelativeBranchNode I)) := by
  let F : CanonicalMap := infiniteStrongPictureCanonicalMap h₀ h₁ h₂ hf
  have hfixF : ∀ j : Nat, j < n → F.level j = j := hfix
  have hcut : F.FixesRelativeCut I :=
    F.fixesRelativeCut_of_fixed_levels I hfixF
  let H : Ordered3Graph Nat := F.imageGraph G.graph
  have hH : H.initialSegment n = I :=
    F.imageGraph_initialCut G.graph I hI hcut
  obtain ⟨eG, hmap, hfixG, hauxG⟩ := hphi.2.2.2 H hH
  let eF : Ordered3Graph.Embedding G.graph H :=
    F.imageGraph_embedding G.graph
  let e : Ordered3Graph.Embedding G.graph G.graph :=
    eG.comp eF
  have hauxF : eF.AuxTypeRespecting :=
    F.imageGraph_auxTypeRespecting G.graph
  refine ⟨e, hauxG.comp hauxF, ?_, ?_⟩
  · intro j hj
    change eG (F.level j) = j
    rw [hfixF j hj]
    exact hfixG j hj
  · intro i
    have hsrc : InRelativeBranchGraph I (G.graph.branchNode i) :=
      G.graph.branchNode_mem_relative I hI i
    have hB : InRelativeBranchGraph I
        (F.mapBranch (G.graph.branchNode i)) :=
      F.mapBranch_preserves_relative I hcut _ hsrc
    refine ⟨hB, ?_⟩
    have hnode :
        (⟨F.mapBranch (G.graph.branchNode i), hB⟩ :
          RelativeBranchNode I) =
        H.relativeBranchNode I hH (F.level i) := by
      apply Subtype.ext
      exact F.mapBranch_branchNode G.graph i
    calc
      e i = eG (F.level i) := rfl
      _ = phi (E.branchIndex H hH (F.level i)) :=
        hmap (F.level i)
      _ = phi (E.code.symm
          (⟨F.mapBranch (G.graph.branchNode i), hB⟩ :
            RelativeBranchNode I)) := by
              rw [hnode]
              rfl

/-- Every actual scalar Milliken strong subtree with its identity
stem protected determines an aux-type-respecting ambient self-
embedding, and its value is literally phi ∘ F_I ∘ g_G on every
generic source vertex. The canonical map comes from the recovered
genuine infinite coordinate pictures. -/
theorem exists_uniform_canonical_selfEmbedding_of_scalar
    (G : GenericEnumerated3Graph)
    {n : Nat} (I : EnumNode n)
    (hI : G.graph.initialSegment n = I)
    (E : SizeFirstBranchPresentation I)
    (phi : Nat → Nat)
    (hphi : UniversalAuxBranchProperty G I E phi)
    (S : StrongSubtree CoordNode.rootGluedAmbientTree)
    (hstem : r (n + 1) S = r (n + 1) scalarIdentity) :
    ∃ e : Ordered3Graph.Embedding G.graph G.graph,
      e.AuxTypeRespecting ∧
      (∀ j : Nat, j < n → e j = j) ∧
      ∃ F : CanonicalMap,
        F.level = CoordNode.millikenCoordinateLevels S ∧
        ∀ i : Nat,
          ∃ hB : InRelativeBranchGraph I
            (F.mapBranch (G.graph.branchNode i)),
            e i = phi (E.code.symm
              (⟨F.mapBranch (G.graph.branchNode i), hB⟩ :
                RelativeBranchNode I)) := by
  obtain ⟨hroot, hfix⟩ :=
    anchoredScalar_root_and_levels S n hstem
  have hf : StrictMono (CoordNode.millikenCoordinateLevels S) :=
    CoordNode.millikenCoordinateLevels_strictMono S
      (CoordNode.millikenStrong_levels_zero_of_root S hroot)
  obtain ⟨r₀, r₁, r₂, h₀, h₁, h₂⟩ :=
    CoordNode.millikenStrong_exists_actual_vector S hroot
  obtain ⟨e, haux, hfixE, hvalue⟩ :=
    exists_uniform_canonical_selfEmbedding_of_vector
      G I hI E phi hphi h₀ h₁ h₂ hf hfix
  let F : CanonicalMap :=
    infiniteStrongPictureCanonicalMap h₀ h₁ h₂ hf
  exact ⟨e, haux, hfixE, F, rfl, hvalue⟩

end ATRFiniteDecoder
end ThreeUniformDiaries
