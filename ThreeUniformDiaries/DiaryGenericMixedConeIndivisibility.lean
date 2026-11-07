import ThreeUniformDiaries.DiaryFiniteSingletonColour
import ThreeUniformDiaries.ActualFiniteAuxRamseyAll
import ThreeUniformDiaries.FiniteAuxEmbeddingPostcomposition

/-!
# Finite vertex colourings admit a generic monochromatic self-copy

The ALREADY VERIFIED unconditional finite ATR Ramsey theorem
applied to a one-vertex source and a protected prefix of length ZERO
should yield the usual indivisibility of the enumerated generic
3-uniform hypergraph:

  every colouring of generic vertices by a finite palette
  has an aux-type-respecting induced generic self-embedding on
  whose range every vertex has the SAME colour.

The only technical input is that ANY target vertex t is the image
of the singleton finite aux embedding with increasing total
extension n ↦ t+n. All finite edge/aux constraints are vacuous
for a source with one actual vertex; the one-type equality is
reflexive because its two source vertices must coincide.

Applying this to the EXISTING checked singletonColour mask
produces a whole induced generic subcopy lying within one complete
mixed singleton-type cone below ANY chosen finite target cut B.

The cone colour is CHOSEN by Ramsey refinement: it may not be
the one needed by a previously fixed source diary stage. This
is not protected relative tail realization or countable diary
unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every target vertex t is an actual finite aux embedding
image of the single-vertex source; its total extension is
strictly increasing, and all nontrivial finite constraints
are vacuous. -/
private def singletonFiniteAuxImage
    (A : EnumNode 1) (G : GenericEnumerated3Graph)
    (t : Nat) :
    Ordered3Graph.FiniteAuxEmbeddingImage
      A.toOrdered3Graph G.graph 1 :=
  Ordered3Graph.FiniteAuxEmbeddingImage.ofFiniteAuxEmbedding
    (fun n : Nat => t + n) {
      strictMono := by
        intro a b hab
        dsimp
        omega
      edge_iff := by
        intro a b c hab hbc hc
        omega
      one := by
        intro w u v _hwu _hwv hu hv
        have hu0 : u = 0 := by omega
        have hv0 : v = 0 := by omega
        subst u
        subst v
        constructor
        · intro _
          intro x y _ _
          exact Iff.rfl
        · intro _
          intro x y _ _
          exact Iff.rfl
      aux := by
        intro w a b c d _hab _hba _hcd _hd _hb _hdd
        omega
    }

@[simp] private theorem singletonFiniteAuxImage_zero
    (A : EnumNode 1) (G : GenericEnumerated3Graph)
    (t : Nat) :
    (singletonFiniteAuxImage A G t).image (0 : Fin 1) = t := by
  rfl

/-- Genuine vertex-colour indivisibility from the kernel-verified
finite ATR Ramsey theorem at the singleton source and zero cut.
The homogeneous subcopy is an induced embedding and is also
aux-type respecting. -/
theorem generic_finite_vertex_colouring_monochromatic
    (G : GenericEnumerated3Graph)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (colour : Nat → κ) :
    ∃ (u : Ordered3Graph.Embedding G.graph G.graph),
      u.AuxTypeRespecting ∧
      ∃ p : κ, ∀ t : Nat, colour (u t) = p := by
  classical
  let A : EnumNode 1 := G.graph.initialSegment 1
  let χ : Ordered3Graph.FiniteAuxEmbeddingImage
        A.toOrdered3Graph G.graph 1 → κ :=
    fun e => colour (e.image (0 : Fin 1))
  obtain ⟨u,hu,_hFix,p,hMono⟩ :=
    ATRFiniteDecoder.actualFiniteAuxRamsey_allFinite
      G (n := 0) (k := 0) (by omega) A χ
  refine ⟨u,hu,p,?_⟩
  intro t
  have hTest := hMono
    (singletonFiniteAuxImage A G t) (by intro i hi; omega)
  change colour
    (((singletonFiniteAuxImage A G t).postcompose u hu).image
      (0 : Fin 1)) = p at hTest
  simpa only [Ordered3Graph.FiniteAuxEmbeddingImage.postcompose_apply,
    singletonFiniteAuxImage_zero] using hTest

/-- The original mixed singleton-type colouring now has an
ENTIRE induced generic hypergraph self-copy in ONE colour cone.
No assumption that an arbitrary specifically designated colour
also contains a generic copy is made. -/
theorem exists_generic_selfcopy_in_one_mixed_singleton_cone
    (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat) (B : Nat)
    (F : Nat → Nat) :
    ∃ (u : Ordered3Graph.Embedding G.graph G.graph),
      u.AuxTypeRespecting ∧
      ∃ p : Fin B → Fin B → Bool,
        ∀ t : Nat,
          DiaryLowerBoundColors.singletonColour K B (F (u t)) = p := by
  exact generic_finite_vertex_colouring_monochromatic G
    (fun t => DiaryLowerBoundColors.singletonColour K B (F t))

end DiaryLeafPriority
end ThreeUniformDiaries
