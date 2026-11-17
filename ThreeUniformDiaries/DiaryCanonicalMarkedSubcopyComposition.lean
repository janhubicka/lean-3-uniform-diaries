import ThreeUniformDiaries.DiaryCanonicalMarkedSubcopy

/-!
# Identity and composition of genuine finite labelled subembeddings

All finite subembedding maps may permute labels; they are checked
using the genuine symmetric unordered hypergraph incidence.
The typed precomposition operation on actual labelled embeddings
has the expected identity and associative composition laws.
This is pure finite relational bookkeeping, independent of
diary axioms, Ramsey theory and the BRS conclusion.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder
open _root_.ThreeUniformDiaries.Ordered3Graph

/-- Every finite enumerated source is an induced labelled copy
of its own zero-extended graph, with the identity label map. -/
theorem finiteLabelledEmbedding_id
    {a : Nat} (A : EnumNode a) :
    IsInducedLabelledCopy A A.toOrdered3Graph
      (fun j : Fin a => j.val) := by
  refine ⟨Fin.val_injective, ?_⟩
  intro i j k hij hjk
  exact (A.toOrdered3Graph.unorderedEdge_iff_of_lt
    i.val j.val k.val hij hjk).symm

/-- Composition of finite induced labelled subembeddings,
including non-monotone label maps. -/
theorem finiteLabelledEmbedding_comp
    {a b c : Nat} (A : EnumNode a) (B : EnumNode b) (C : EnumNode c)
    (i : Fin b → Fin a)
    (j : Fin c → Fin b)
    (hi : IsInducedLabelledCopy B A.toOrdered3Graph
      (fun t => (i t).val))
    (hj : IsInducedLabelledCopy C B.toOrdered3Graph
      (fun t => (j t).val)) :
    IsInducedLabelledCopy C A.toOrdered3Graph
      (fun t => (i (j t)).val) :=
  isInducedLabelledCopy_precompose
    B C A.toOrdered3Graph j hj (fun t => (i t).val) hi

/-- Restricting an actual labelled copy by the identity does
not change that copy. -/
theorem GenuineFiniteEmbeddings.precompose_id
    {U : Ordered3Graph Nat} {a : Nat} {A : EnumNode a}
    (v : GenuineFiniteEmbeddings A U) :
    v.precompose (fun j : Fin a => j)
      (finiteLabelledEmbedding_id A) = v := by
  apply Subtype.ext
  rfl

/-- Two consecutive restrictions of actual labelled embeddings
are the same as one restriction by the composite map. -/
theorem GenuineFiniteEmbeddings.precompose_comp
    {U : Ordered3Graph Nat} {a b c : Nat}
    {A : EnumNode a} {B : EnumNode b} {C : EnumNode c}
    (v : GenuineFiniteEmbeddings A U)
    (i : Fin b → Fin a) (j : Fin c → Fin b)
    (hi : IsInducedLabelledCopy B A.toOrdered3Graph
      (fun t => (i t).val))
    (hj : IsInducedLabelledCopy C B.toOrdered3Graph
      (fun t => (j t).val)) :
    (v.precompose i hi).precompose j hj =
      v.precompose (fun t => i (j t))
        (finiteLabelledEmbedding_comp A B C i j hi hj) := by
  apply Subtype.ext
  rfl

end ATRFiniteDecoder
end ThreeUniformDiaries
