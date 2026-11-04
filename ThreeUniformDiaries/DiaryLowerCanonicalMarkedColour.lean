import ThreeUniformDiaries.DiaryLowerCanonicalMarkedShape
import ThreeUniformDiaries.DiaryFiniteLowerEnumRecovery

/-!
# Track C lower: uniqueness and totality of the canonical marked diary colour

A finite labelled leaf tuple in a full countable diary determines its
sorted leaf-meet support, the entire induced finite source graph, and
the marked ranks of each labelled vertex. These three pieces determine
one actual MarkedFiniteSource 0 a *literally*, including its dependent
EnumNode representation; the proof does not identify two merely
unlabelled-isomorphic diaries.

The extracted source from the checked Track C totality theorem is
therefore unique. We construct an actual total colouring of genuine
labelled A-embeddings in an arbitrary U, given an induced unordered
leaf embedding F : U -> K into a full diary K.

No universal colouring-unavoidability is assumed or proved here.
Its proof still requires real finite copies in every prescribed
selfembedding's leaf range and exact transport of the source marks.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- Once full cardinality, the zero-extended induced finite
source graph, and all genuine mark indices are fixed, there is
at most ONE dependent marked finite source record. This also
handles empty or singleton labelled A without hidden injective
enumeration assumptions. -/
theorem markedSource_eq_of_same_canonical_support
    {a : Nat} (T₁ T₂ : MarkedFiniteSource 0 a)
    (S : Finset Nat) (H : Ordered3Graph Nat)
    (v : Fin a → Nat)
    (hSize₁ : T₁.source.k + 1 = S.card)
    (hSize₂ : T₂.source.k + 1 = S.card)
    (hGraph₁ : T₁.source.picture.toOrdered3Graph = H)
    (hGraph₂ : T₂.source.picture.toOrdered3Graph = H)
    (hIndices₁ : ∀ i : Fin a,
      finiteSupportIndex S (T₁.marked i).val = v i)
    (hIndices₂ : ∀ i : Fin a,
      finiteSupportIndex S (T₂.marked i).val = v i) :
    T₁ = T₂ := by
  classical
  have hk : T₁.source.k = T₂.source.k := by omega
  have hMarks : ∀ i : Fin a,
      (T₁.marked i).val = (T₂.marked i).val := by
    intro i
    have hi₁ : (T₁.marked i).val < S.card := by
      rw [← hSize₁]
      exact (T₁.marked i).isLt
    have hi₂ : (T₂.marked i).val < S.card := by
      rw [← hSize₂]
      exact (T₂.marked i).isLt
    have hEqualIndex :
        finiteSupportIndex S (T₁.marked i).val =
        finiteSupportIndex S (T₂.marked i).val :=
      (hIndices₁ i).trans (hIndices₂ i).symm
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hstrict :=
        finiteSupportIndex_strictMono S
          (T₁.marked i).val (T₂.marked i).val hlt hi₂
      omega
    · have hstrict :=
        finiteSupportIndex_strictMono S
          (T₂.marked i).val (T₁.marked i).val hgt hi₁
      omega
  cases T₁ with
  | mk source₁ marked₁ =>
    cases T₂ with
    | mk source₂ marked₂ =>
      cases source₁ with
      | mk k₁ picture₁ cut₁ =>
        cases source₂ with
        | mk k₂ picture₂ cut₂ =>
          change k₁ = k₂ at hk
          subst k₂
          have hSameGraph :
              picture₁.toOrdered3Graph = picture₂.toOrdered3Graph :=
            hGraph₁.trans hGraph₂.symm
          have hSamePicture : picture₁ = picture₂ := by
            calc
              picture₁ =
                  picture₁.toOrdered3Graph.initialSegment (k₁ + 1) :=
                (EnumNode.initialSegment_toOrdered3Graph_self picture₁).symm
              _ = picture₂.toOrdered3Graph.initialSegment (k₁ + 1) := by
                rw [hSameGraph]
              _ = picture₂ :=
                EnumNode.initialSegment_toOrdered3Graph_self picture₂
          cases hSamePicture
          have hSameMarks : marked₁ = marked₂ := by
            funext i
            apply Fin.ext
            exact hMarks i
          cases hSameMarks
          rfl

/-- The actual marked source extracted from a labelled finite
leaf tuple, selected once and for all from the proved existence
theorem. Its picture and marking are in fact UNIQUE by the
preceding theorem, so no arbitrary choices of a diary shape
remain in the resulting colour. -/
noncomputable def canonicalMarkedSourceOfLeaves
    {K : Ordered3Graph Nat} (D : RoleDiary K)
    {a : Nat} (A : EnumNode a)
    (v : Fin a → Nat)
    (hLeaf : ∀ i : Fin a, IsLeaf K (v i))
    (hCopy : IsInducedLabelledCopy A K v) :
    MarkedFiniteSource 0 a :=
  Classical.choose
    (exists_genuineMarkedDiary_of_labelledLeafCopy
      D A v hLeaf hCopy)

/-- Exactly the finite membership, support-cardinality,
source-graph, and every-labelled-rank properties of the chosen
source. The entire statement is verified, not a hypothesis
attached to a definition. -/
theorem canonicalMarkedSourceOfLeaves_spec
    {K : Ordered3Graph Nat} (D : RoleDiary K)
    {a : Nat} (A : EnumNode a)
    (v : Fin a → Nat)
    (hLeaf : ∀ i : Fin a, IsLeaf K (v i))
    (hCopy : IsInducedLabelledCopy A K v) :
    let T := canonicalMarkedSourceOfLeaves D A v hLeaf hCopy
    T ∈ allGenuineMarkedDiaryFinset A ∧
      T.source.k + 1 =
        (finiteLeafMeetSupport K
          ((Finset.univ : Finset (Fin a)).image v)).card ∧
      T.source.picture.toOrdered3Graph =
        finiteSupportGraph K
          (finiteLeafMeetSupport K
            ((Finset.univ : Finset (Fin a)).image v)) ∧
      (∀ i : Fin a,
        finiteSupportIndex
          (finiteLeafMeetSupport K
            ((Finset.univ : Finset (Fin a)).image v))
          (T.marked i).val = v i) := by
  classical
  exact Classical.choose_spec
    (exists_genuineMarkedDiary_of_labelledLeafCopy
      D A v hLeaf hCopy)

/-- Any genuine finite marked-source record with the same exact
support picture and labelled indices as the canonical source is
the canonical source *literally*, not just isomorphic to it. -/
theorem canonicalMarkedSourceOfLeaves_eq_of_spec
    {K : Ordered3Graph Nat} (D : RoleDiary K)
    {a : Nat} (A : EnumNode a)
    (v : Fin a → Nat)
    (hLeaf : ∀ i : Fin a, IsLeaf K (v i))
    (hCopy : IsInducedLabelledCopy A K v)
    (T : MarkedFiniteSource 0 a)
    (hSize : T.source.k + 1 =
      (finiteLeafMeetSupport K
        ((Finset.univ : Finset (Fin a)).image v)).card)
    (hGraph : T.source.picture.toOrdered3Graph =
      finiteSupportGraph K
        (finiteLeafMeetSupport K
          ((Finset.univ : Finset (Fin a)).image v)))
    (hIndices : ∀ i : Fin a,
      finiteSupportIndex
        (finiteLeafMeetSupport K
          ((Finset.univ : Finset (Fin a)).image v))
        (T.marked i).val = v i) :
    canonicalMarkedSourceOfLeaves D A v hLeaf hCopy = T := by
  classical
  let S : Finset Nat :=
    finiteLeafMeetSupport K
      ((Finset.univ : Finset (Fin a)).image v)
  let H : Ordered3Graph Nat := finiteSupportGraph K S
  obtain ⟨_hMem, hCanonSize, hCanonGraph, hCanonIndices⟩ :=
    canonicalMarkedSourceOfLeaves_spec D A v hLeaf hCopy
  exact markedSource_eq_of_same_canonical_support
    (canonicalMarkedSourceOfLeaves D A v hLeaf hCopy)
    T S H v hCanonSize hSize hCanonGraph hGraph
    hCanonIndices hIndices

/-- A *single total finite colouring* of ACTUAL labelled
A-embeddings in U, provided U is embedded into the genuine leaves
of a full countable RoleDiary K. This is the lower-degree colouring
candidate with the true finite marked-diary type palette;
no extra ordinal ordering of source A and no Aut(A) factor is added. -/
noncomputable def canonicalMarkedDiaryColour
    {U K : Ordered3Graph Nat} (D : RoleDiary K)
    (F : UnorderedEmbedding U K)
    (hFLeaf : ∀ x : Nat, IsLeaf K (F x))
    {a : Nat} (A : EnumNode a) :
    GenuineFiniteEmbeddings A U → GenuineMarkedDiaryTypes A :=
  fun v => by
    classical
    let w : Fin a → Nat := fun i => F (v.val i)
    have hLeaf : ∀ i : Fin a, IsLeaf K (w i) :=
      fun i => hFLeaf (v.val i)
    have hCopy : IsInducedLabelledCopy A K w :=
      isInducedLabelledCopy_map_unordered A F v.val v.property
    exact ⟨canonicalMarkedSourceOfLeaves D A w hLeaf hCopy,
      (canonicalMarkedSourceOfLeaves_spec D A w hLeaf hCopy).1⟩

end ATRFiniteDecoder
end ThreeUniformDiaries
