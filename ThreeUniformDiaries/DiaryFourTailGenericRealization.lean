import ThreeUniformDiaries.DiaryFiniteThreeTailAmalgam
import ThreeUniformDiaries.DiaryGenericFixedTwoEmbedding
import ThreeUniformDiaries.DiaryFinitePointedEnumNode

/-!
# A four-tail native source has a generic type-respecting copy

The four-tail edge amalgam is a finite source whose complete initial
prefix is LITERALLY the corresponding prefix of the generic graph.
This is because both original three-tail source pictures were
obtained by prefix-fixing compression of G, and the free amalgam
preserves the first source on that entire prefix.

The already verified universal fixed-prefix K_I theorem therefore
supplies a genuinely increasing induced type-respecting embedding
of the entire FOUR-tail source into the generic graph which fixes
the protected prefix pointwise. No additional Ramsey theorem,
genericity axiom, or global type-meet preservation across omitted
levels is needed.

The still-open step is separate: show that the two original
three-tail finite ATR codes embed into the common four-tail source
as ATR codes, not merely as induced-edge subpictures.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Literal equality of the finite initial enumerated pictures
follows from induced edge agreement on increasing triples of
the relevant finite prefix. Neither graph is required to be
generic or finite outside that prefix. -/
theorem initialSegment_eq_of_prefix_edge_agreement
    (H K : Ordered3Graph Nat) (n : Nat)
    (hEdge : ∀ x y z, x < y → y < z → z < n →
      (H.edge x y z ↔ K.edge x y z)) :
    H.initialSegment n = K.initialSegment n := by
  classical
  apply EnumNode.ext_triples
  funext x y z
  by_cases hvalid : x < y ∧ y < z ∧ z < n
  · have hh := H.initialSegment_edge_iff
      hvalid.1 hvalid.2.1 hvalid.2.2
    have hk := K.initialSegment_edge_iff
      hvalid.1 hvalid.2.1 hvalid.2.2
    have hEq :
        ((H.initialSegment n).triple x y z = true) ↔
        ((K.initialSegment n).triple x y z = true) := by
      exact hh.trans
        ((hEdge x y z hvalid.1 hvalid.2.1 hvalid.2.2).trans hk.symm)
    cases hH : (H.initialSegment n).triple x y z <;>
      cases hK : (K.initialSegment n).triple x y z <;>
      simp_all
  · calc
      (H.initialSegment n).triple x y z = false :=
        (H.initialSegment n).support x y z hvalid
      _ = (K.initialSegment n).triple x y z :=
        ((K.initialSegment n).support x y z hvalid).symm

/-- The native four-tail free amalgam of two compressed generic
three-tail pictures has the exact same initial segment of
length j as the generic graph, with no additional hypothesis
on the two exterior pictures. -/
theorem threeTailGenericFreeAmalgam_prefix
    (G : GenericEnumerated3Graph)
    (j m n a b c d : Nat) :
    let A := G.graph.pullback (threeTailInsertion j m a b)
    let B := G.graph.pullback (threeTailInsertion j n c d)
    let C := threeTailFreeAmalgam A B j
    C.initialSegment j = G.graph.initialSegment j := by
  let f := threeTailInsertion j m a b
  let A := G.graph.pullback f
  let B := G.graph.pullback (threeTailInsertion j n c d)
  let C := threeTailFreeAmalgam A B j
  apply initialSegment_eq_of_prefix_edge_agreement C G.graph j
  intro x y z hxy hyz hz
  have hx : x < j := by omega
  have hy : y < j := by omega
  have hLeft : C.edge x y z ↔ A.edge x y z :=
    threeTailFreeAmalgam_left A B j x y z (by omega)
  change C.edge x y z ↔
    G.graph.edge (f x) (f y) (f z) at hLeft
  simpa only [f,
    threeTailInsertion_fix_prefix j m a b x hx,
    threeTailInsertion_fix_prefix j m a b y hy,
    threeTailInsertion_fix_prefix j m a b z hz] using hLeft

/-- REALIZE the entire four-tail finite source inside G by one
induced, type-respecting embedding fixing its full generic
prefix, using the already checked universal fixed-prefix
embedding lemma. The source's exterior vertices are not
artificially required to fill consecutive levels of G. -/
theorem exists_typeRespecting_fourTail_generic_copy
    (G : GenericEnumerated3Graph)
    (j m n a b c d : Nat) (hj : 0 < j) :
    let A := G.graph.pullback (threeTailInsertion j m a b)
    let B := G.graph.pullback (threeTailInsertion j n c d)
    let C := threeTailFreeAmalgam A B j
    ∃ χ : Embedding C G.graph,
      χ.TypeRespecting ∧ ∀ k, k < j → χ k = k := by
  let A := G.graph.pullback (threeTailInsertion j m a b)
  let B := G.graph.pullback (threeTailInsertion j n c d)
  let C := threeTailFreeAmalgam A B j
  have hInit : C.initialSegment j = G.graph.initialSegment j :=
    threeTailGenericFreeAmalgam_prefix G j m n a b c d
  exact ATRFiniteDecoder.exists_typeRespecting_embedding_fix_prefix
    G C j hj hInit

end Ordered3Graph
end ThreeUniformDiaries
