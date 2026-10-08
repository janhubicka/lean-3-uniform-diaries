import ThreeUniformDiaries.FiniteInheritedStage
import ThreeUniformDiaries.InfinitePrefixes

/-!
# Initialise the generic embedding recursion at a fixed initial segment

Lemma Kiemb requires the target map to be the identity on the first
n vertices. When the source and target agree on the first n vertices,
their literal identity embedding forms a finite generic stage. The
repaired inherited extension can then be iterated from this stage,
without moving the fixed initial segment.

This is the base case for the K_I recursion, complementary to the
one-vertex zero base in CountableInheritedEmbedding.
-/

namespace ThreeUniformDiaries
namespace GenericEnumerated3Graph

/-- The literal identity on a common finite initial segment is a
strictly increasing induced finite embedding with bound n. -/
def fixedPrefixStage
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (n : Nat)
    (hI : K.initialSegment n = G.graph.initialSegment n) :
    FiniteGenericStage G K n where
  bound := n
  image := fun i => i
  mono := by
    intro i j hij
    exact hij
  edge_iff := by
    intro i j k hij hjk
    have hK := K.initialSegment_edge_iff hij hjk k.isLt
    have hG := G.graph.initialSegment_edge_iff hij hjk k.isLt
    calc
      K.edge i.val j.val k.val ↔
          (K.initialSegment n).triple i.val j.val k.val = true :=
        hK.symm
      _ ↔ (G.graph.initialSegment n).triple i.val j.val k.val =
          true := by rw [hI]
      _ ↔ G.graph.edge i.val j.val k.val := hG

/-- The initial stage fixes every vertex below n exactly. -/
theorem fixedPrefixStage_image
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (n : Nat)
    (hI : K.initialSegment n = G.graph.initialSegment n)
    (i : Fin n) :
    ((G.fixedPrefixStage K n hI).image i).val = i.val := rfl

/-- Extending the initial stage using the strengthened prescription
preserves the entire common initial segment. -/
theorem fixedPrefixStage_extend_old
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (n : Nat)
    (hI : K.initialSegment n = G.graph.initialSegment n)
    (parent : Fin n) (i : Fin n) :
    (((G.fixedPrefixStage K n hI).extendInherited parent).image
      (Fin.castSucc i)).val = i.val := by
  simpa [fixedPrefixStage_image] using
    (FiniteGenericStage.extendInherited_old
      (G.fixedPrefixStage K n hI) parent i)

end GenericEnumerated3Graph
end ThreeUniformDiaries
