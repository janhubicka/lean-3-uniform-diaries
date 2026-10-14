import ThreeUniformDiaries.DiaryOrientationReplacement
import ThreeUniformDiaries.DiaryCompleteNativeStabilisation

/-!
# The five-vertex gadget in the cut-zero orientation argument

The manuscript uses a five-vertex induced pattern with the single
edge {0,1,3}. The local orientation calculation is independent of
diary roles: an early disagreement between the singleton types of
2 and 3 bounds their meet by the image of vertex 1, while the
stabilised agreement of the singleton types of 2 and 4 through that
cut permits replacing 2 by 4 in the comparison with 3.

The gadget is represented as a countable ordered hypergraph with
only the indicated increasing triple as an edge, so the statements
can be used with the existing `Ordered3Graph.Embedding` API.
Only its first five vertices are used.

Crucially, the external lower-bound map F is NOT represented by an
order-preserving `Ordered3Graph.Embedding`. A separate result below
derives the necessary close singleton types from the actual
I1/I2-verified fused embedding, while the two target edge bits are
supplied explicitly. Those edge bits follow when F is the required
(unordered) hypergraph embedding; we do not silently assume them
for an arbitrary injection.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- The manuscript's five-vertex orientation gadget, extended by
isolated vertices to use the natural-number enumeration API. -/
def fiveVertexOrientationGadget : Ordered3Graph Nat where
  edge i j k := i = 0 ∧ j = 1 ∧ k = 3

/-- The two vertices 2 and 4 have identical singleton 1-types
below the cut 2 in this gadget. -/
theorem fiveVertexOrientationGadget_oneType_2_4 :
    fiveVertexOrientationGadget.SameOneTypeBelow 2 2 4 := by
  intro a b hab hb
  have hb1 : b = 1 := by omega
  have ha0 : a = 0 := by omega
  subst a
  subst b
  simp [fiveVertexOrientationGadget]

/-- The exact local five-vertex orientation calculation.
There is one edge disagreement at the early marker 0,1, and
the images of 2,4 have equal singleton type through image(1)+1.

The increasing map may be any map, not necessarily a hypergraph
embedding: the necessary target edge/nonedge conditions are explicit. -/
theorem fiveVertex_orientation_of_target_bits
    (K : Ordered3Graph Nat)
    (φ : Nat → Nat) (hφ : StrictMono φ)
    (h23 : ¬ K.edge (φ 0) (φ 1) (φ 2))
    (h33 : K.edge (φ 0) (φ 1) (φ 3))
    (hclose : K.SameOneTypeBelow (φ 1 + 1) (φ 2) (φ 4)) :
    DiaryLeafPriority.LexEarlier K (φ 2) (φ 3) ↔
      DiaryLeafPriority.LexEarlier K (φ 4) (φ 3) := by
  have h01 : φ 0 < φ 1 := hφ (by omega)
  have h12 : φ 1 < φ 2 := hφ (by omega)
  have h13 : φ 1 < φ 3 := hφ (by omega)
  have h14 : φ 1 < φ 4 := hφ (by omega)
  have hdiff :
      ¬ (K.edge (φ 0) (φ 1) (φ 2) ↔
          K.edge (φ 0) (φ 1) (φ 3)) := by
    intro h
    exact h23 (h.mpr h33)
  have hmeet : K.oneMeetLevel (φ 2) (φ 3) ≤ φ 1 :=
    K.oneMeetLevel_le_of_edge_disagreement
      (φ 2) (φ 3) (φ 0) (φ 1) h01 hdiff
  exact K.lexEarlier_stable_under_close_one_types
    (φ 1) (φ 2) (φ 3) (φ 4)
    h12 h13 h14 hclose hmeet

/-- An actual ordered induced copy of the single-edge five-vertex
gadget satisfies the two target edge bits automatically. -/
theorem fiveVertex_orientation_of_embedding
    {K : Ordered3Graph Nat}
    (φ : Embedding fiveVertexOrientationGadget K)
    (hclose : K.SameOneTypeBelow (φ 1 + 1) (φ 2) (φ 4)) :
    DiaryLeafPriority.LexEarlier K (φ 2) (φ 3) ↔
      DiaryLeafPriority.LexEarlier K (φ 4) (φ 3) := by
  have hYes : K.edge (φ 0) (φ 1) (φ 3) :=
    (φ.edge_iff (by omega) (by omega)).mp
      (by simp [fiveVertexOrientationGadget])
  have hNo : ¬ K.edge (φ 0) (φ 1) (φ 2) := by
    intro h
    have hsource : fiveVertexOrientationGadget.edge 0 1 2 :=
      (φ.edge_iff (by omega) (by omega)).mpr h
    simpa [fiveVertexOrientationGadget] using hsource
  exact K.fiveVertex_orientation_of_target_bits
    φ.toFun φ.strictMono hNo hYes hclose

end Ordered3Graph

namespace ATRFiniteDecoder

open Ordered3Graph

/-- Applying the verified I2 theorem to a type-respecting copy
of the five-vertex gadget yields precisely the target cut needed
for the orientation replacement lemma.

This step does not assume that the external injective map F
preserves hyperedges or enumeration order. -/
theorem fiveVertex_gadget_close_types_after_fusion
    (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F)
    (ψ : Embedding fiveVertexOrientationGadget G.graph)
    (hψ : ψ.TypeRespecting) :
    let g := orderedDiaryFusion G K F hF
    K.SameOneTypeBelow
      (F (g (ψ 1)) + 1)
      (F (g (ψ 2))) (F (g (ψ 4))) := by
  let g := orderedDiaryFusion G K F hF
  have hψ12 : ψ 1 < ψ 2 := ψ.strictMono (by omega)
  have hψ24 : ψ 2 ≤ ψ 4 :=
    (ψ.strictMono (by omega)).le
  have hpositive : 0 < ψ 2 := by omega
  have hsource : G.graph.SameOneTypeBelow
      (ψ 2) (ψ 2) (ψ 4) :=
    (hψ.one 2 2 4 (by omega) (by omega)).mp
      fiveVertexOrientationGadget_oneType_2_4
  have hI2 : K.SameOneTypeBelow
      (F (g (ψ 2 - 1)) + 1)
      (F (g (ψ 2))) (F (g (ψ 4))) :=
    orderedDiaryFusion_singletonType_stabilised
      G K F hF (ψ 2) hpositive
      (ψ 2) (ψ 4) (le_refl _) hψ24 hsource
  have hOrder : StrictMono (fun t => F (g t)) :=
    (orderedDiaryFusion_complete_native_stabilisation
      G K F hF).2.1
  have hpred : ψ 1 ≤ ψ 2 - 1 := by omega
  have hcut : F (g (ψ 1)) ≤ F (g (ψ 2 - 1)) :=
    hOrder.monotone hpred
  intro a b hab hb
  apply hI2 hab
  omega

/-- Conditional target orientation conclusion for the actual
fused generic image of the five-vertex gadget. I1 supplies the
target order, I2 supplies the close singleton types, and the
two explicit target edge bits are the only needed contribution
of the outer map's relational embedding property. -/
theorem fiveVertex_orientation_after_fusion
    (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F)
    (ψ : Embedding fiveVertexOrientationGadget G.graph)
    (hψ : ψ.TypeRespecting)
    (hEdge :
      K.edge
        (F (orderedDiaryFusion G K F hF (ψ 0)))
        (F (orderedDiaryFusion G K F hF (ψ 1)))
        (F (orderedDiaryFusion G K F hF (ψ 3))))
    (hNonedge :
      ¬ K.edge
        (F (orderedDiaryFusion G K F hF (ψ 0)))
        (F (orderedDiaryFusion G K F hF (ψ 1)))
        (F (orderedDiaryFusion G K F hF (ψ 2)))) :
    DiaryLeafPriority.LexEarlier K
      (F (orderedDiaryFusion G K F hF (ψ 2)))
      (F (orderedDiaryFusion G K F hF (ψ 3))) ↔
    DiaryLeafPriority.LexEarlier K
      (F (orderedDiaryFusion G K F hF (ψ 4)))
      (F (orderedDiaryFusion G K F hF (ψ 3))) := by
  let g := orderedDiaryFusion G K F hF
  have hOrder : StrictMono (fun t => F (g t)) :=
    (orderedDiaryFusion_complete_native_stabilisation
      G K F hF).2.1
  have hφ : StrictMono (fun t => F (g (ψ t))) :=
    hOrder.comp ψ.strictMono
  have hclose : K.SameOneTypeBelow
      (F (g (ψ 1)) + 1)
      (F (g (ψ 2))) (F (g (ψ 4))) :=
    fiveVertex_gadget_close_types_after_fusion
      G K F hF ψ hψ
  exact K.fiveVertex_orientation_of_target_bits
    (fun t => F (g (ψ t))) hφ hNonedge hEdge hclose

end ATRFiniteDecoder
end ThreeUniformDiaries
