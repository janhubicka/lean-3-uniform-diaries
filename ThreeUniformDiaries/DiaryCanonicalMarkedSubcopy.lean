import ThreeUniformDiaries.DiaryCanonicalMarkedNaturality

/-!
# Genuine labelled finite subembeddings, including label permutations

The canonical big Ramsey colouring is on actual INDUCED labelled
embeddings, not arbitrary tuples. A finite labelled inclusion
i:B -> A can scramble the numerical order of source labels.
It is enough to test i using the unordered symmetric ternary
relation of A, then compose with a genuine labelled A-embedding.

The existing equivalence between increasing-triple and full
unordered-labelled-copy predicates supplies exact inducedness,
including nonedges and all six permutations, with no false
order-preservation hypothesis.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open _root_.ThreeUniformDiaries.Ordered3Graph

/-- Composing two genuinely induced finite labelled embeddings
remains a genuine induced labelled copy even when the inner
embedding does not preserve the respective enumerations. -/
theorem isInducedLabelledCopy_precompose
    {a b : Nat} (A : EnumNode a) (B : EnumNode b)
    (U : Ordered3Graph Nat)
    (i : Fin b → Fin a)
    (hi : IsInducedLabelledCopy B A.toOrdered3Graph
      (fun j => (i j).val))
    (v : Fin a → Nat)
    (hv : IsInducedLabelledCopy A U v) :
    IsInducedLabelledCopy B U (fun j => v (i j)) := by
  have hvFull :
      IsFiniteLabelledCopy A.toOrdered3Graph U a v :=
    (isInducedLabelledCopy_iff_fullUnordered A U v).mp hv
  refine ⟨?_, ?_⟩
  · intro j k heq
    have hik : i j = i k := hv.1 heq
    exact hi.1 (congrArg Fin.val hik)
  · intro j k l hjk hkl
    exact (hi.2 j k l hjk hkl).trans
      (hvFull.2 (i j) (i k) (i l))

/-- Typed restriction of an actual labelled A-embedding along
any genuine finite B -> A embedding, including permutations. -/
def GenuineFiniteEmbeddings.precompose
    {U : Ordered3Graph Nat} {a b : Nat}
    {A : EnumNode a} {B : EnumNode b}
    (v : GenuineFiniteEmbeddings A U)
    (i : Fin b → Fin a)
    (hi : IsInducedLabelledCopy B A.toOrdered3Graph
      (fun j => (i j).val)) :
    GenuineFiniteEmbeddings B U :=
  ⟨fun j => v.val (i j),
    isInducedLabelledCopy_precompose A B U i hi v.val v.property⟩

end ATRFiniteDecoder
end ThreeUniformDiaries
