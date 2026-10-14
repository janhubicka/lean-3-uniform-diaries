import ThreeUniformDiaries.DiaryFiveVertexOrientationGadget
import ThreeUniformDiaries.DiaryUnorderedEmbedding
import ThreeUniformDiaries.UniversalAuxBranchEmbedding

/-!
# The cut-zero orientation gadget under an actual unordered outer embedding

The verified native stabilisation theorem starts with an arbitrary
injective map of enumerated vertices, then produces a self-embedding
whose outer image is increasing. The manuscript's outer map is
additionally a relation embedding of the UNORDERED underlying
3-hypergraph. This is essential for transporting the edge/nonedge
witnesses of the five-vertex orientation gadget.

The concrete cut-zero gadget has only the edge (0,1,3).
A type-respecting generic copy exists by the already verified
universal countable aux-embedding theorem with empty protected prefix.
The outer unordered embedding preserves and reflects both its edge
(0,1,3) and its nonedge (0,1,2), after the stabilised outer image
has become increasing. The previously verified local calculation
then equates the two target lexicographic comparisons (2,3)
and (4,3).

These theorems discharge the gadget's existence and target edge-bit
assumptions. They do NOT by themselves assert global orientation
synchronisation for all diary leaf pairs: the common-gadget
amalgamation connecting arbitrary pairs is still a separate lemma.
-/

namespace ThreeUniformDiaries

namespace ATRFiniteDecoder

open Ordered3Graph

/-- The generic graph contains a type-respecting induced copy
of the concrete five-vertex gadget FIXING BOTH initial marker
vertices 0 and 1, as required in the manuscript. Any two-vertex
enumerated prefix is edgeless, so the source and target prefixes
are automatically identical. Apply the universal fixed-prefix
auxiliary branch embedding at n=2. -/
theorem exists_typeRespecting_fiveVertex_gadget_fix_two
    (G : GenericEnumerated3Graph) :
    ∃ ψ : Embedding fiveVertexOrientationGadget G.graph,
      ψ.TypeRespecting ∧ ψ 0 = 0 ∧ ψ 1 = 1 := by
  let I : EnumNode 2 := G.graph.initialSegment 2
  obtain ⟨E, phi, hproperty⟩ :=
    exists_universal_fixedAuxEmbedding G I (by omega) rfl
  have hI : fiveVertexOrientationGadget.initialSegment 2 = I := by
    apply EnumNode.ext_triples
    funext a b c
    have hbad : ¬ (a < b ∧ b < c ∧ c < 2) := by omega
    calc
      (fiveVertexOrientationGadget.initialSegment 2).triple a b c =
          false :=
        (fiveVertexOrientationGadget.initialSegment 2).support a b c hbad
      _ = I.triple a b c :=
        ((G.graph.initialSegment 2).support a b c hbad).symm
  obtain ⟨ψ, _, hfix, haux⟩ :=
    hproperty.2.2.2 fiveVertexOrientationGadget hI
  exact ⟨ψ, haux.typeRespecting,
    hfix 0 (by omega), hfix 1 (by omega)⟩

/-- Forgetting the fixed markers yields the simpler type-respecting
copy interface used by the unconditional orientation calculation. -/
theorem exists_typeRespecting_fiveVertex_gadget
    (G : GenericEnumerated3Graph) :
    ∃ ψ : Embedding fiveVertexOrientationGadget G.graph,
      ψ.TypeRespecting := by
  obtain ⟨ψ, hψ, _, _⟩ :=
    exists_typeRespecting_fiveVertex_gadget_fix_two G
  exact ⟨ψ, hψ⟩

/-- The target orientation identity of the five-vertex gadget
follows unconditionally for a genuine unordered outer
hypergraph embedding. No order is assumed of that outer map. -/
theorem fiveVertex_orientation_after_unordered_fusion
    (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (ψ : Embedding fiveVertexOrientationGadget G.graph)
    (hψ : ψ.TypeRespecting) :
    let g := orderedDiaryFusion G K F.toFun F.injective
    DiaryLeafPriority.LexEarlier K
      (F (g (ψ 2))) (F (g (ψ 3))) ↔
    DiaryLeafPriority.LexEarlier K
      (F (g (ψ 4))) (F (g (ψ 3))) := by
  let g := orderedDiaryFusion G K F.toFun F.injective
  have horder : StrictMono (fun t => F (g t)) :=
    (orderedDiaryFusion_complete_native_stabilisation
      G K F.toFun F.injective).2.1
  have hsourceEdge :
      G.graph.edge (ψ 0) (ψ 1) (ψ 3) :=
    (ψ.edge_iff (by omega) (by omega)).mp
      (by simp [fiveVertexOrientationGadget])
  have hsourceNonedge :
      ¬ G.graph.edge (ψ 0) (ψ 1) (ψ 2) := by
    intro h
    have hs : fiveVertexOrientationGadget.edge 0 1 2 :=
      (ψ.edge_iff (by omega) (by omega)).mpr h
    simpa [fiveVertexOrientationGadget] using hs
  have hedge :
      K.edge (F (g (ψ 0))) (F (g (ψ 1))) (F (g (ψ 3))) :=
    (F.composed_ordered_edges g horder
      (ψ 0) (ψ 1) (ψ 3)
      (ψ.strictMono (by omega))
      (ψ.strictMono (by omega))).mp hsourceEdge
  have hnonedge :
      ¬ K.edge (F (g (ψ 0))) (F (g (ψ 1))) (F (g (ψ 2))) := by
    intro h
    exact hsourceNonedge
      ((F.composed_ordered_edges g horder
        (ψ 0) (ψ 1) (ψ 2)
        (ψ.strictMono (by omega))
        (ψ.strictMono (by omega))).mpr h)
  exact fiveVertex_orientation_after_fusion
    G K F.toFun F.injective ψ hψ hedge hnonedge

/-- An actual generic gadget and its stabilised orientation
calculation exist for every unordered outer hypergraph embedding.
This removes the two formerly conditional witness requirements. -/
theorem exists_fiveVertex_orientation_after_unordered_fusion
    (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K) :
    ∃ ψ : Embedding fiveVertexOrientationGadget G.graph,
      ψ.TypeRespecting ∧
      (let g := orderedDiaryFusion G K F.toFun F.injective
       DiaryLeafPriority.LexEarlier K
         (F (g (ψ 2))) (F (g (ψ 3))) ↔
       DiaryLeafPriority.LexEarlier K
         (F (g (ψ 4))) (F (g (ψ 3)))) := by
  obtain ⟨ψ, hψ⟩ :=
    exists_typeRespecting_fiveVertex_gadget G
  exact ⟨ψ, hψ,
    fiveVertex_orientation_after_unordered_fusion G K F ψ hψ⟩

end ATRFiniteDecoder
end ThreeUniformDiaries
