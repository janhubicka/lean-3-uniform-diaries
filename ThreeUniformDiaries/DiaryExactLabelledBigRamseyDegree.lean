import ThreeUniformDiaries.DiaryLowerExactCountUnconditionalLeafModel
import ThreeUniformDiaries.DiaryUpperBoundByOrderedDiarySum

/-!
# Track C: exact labelled big Ramsey bound, as a quantified predicate

For finite labelled A, an integer t is a big Ramsey upper bound if
EVERY finite colouring of the ACTUAL labelled induced copies of A in U
has an induced unordered self-copy on which at most t colours remain.
We express palettes by finite sets, not by a potentially duplicate list.

The checked sharp upper theorem supplies the bound
  N(A) = (sum over ALL increasing presentations P of unordered A
          of the number of genuine full diaries of P) * |Aut(A)|.
The checked lower theorem supplies one concrete unavoidable
colouring by all genuine marked diary types. We embed that
possibly empty colour type into Option to satisfy the required
nonempty finite-colour convention WITHOUT asserting that A has a
diary in the special small-cardinality cases.

It follows that t is a labelled big Ramsey bound IFF N(A) <= t.
Thus N(A) is the exact minimal labelled big Ramsey bound, provided
an enumerated generic G. This theorem does not use or assert the
stronger countable-source diary-unavoidability theorem.

The parameter G will be removed only after the independent
enumerated-generic existence theorem is exact-head Lean-verified.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open _root_.ThreeUniformDiaries.Ordered3Graph

/-- The literal finite-colouring definition of a labelled big
Ramsey bound for the underlying *unordered* 3-hypergraph U.
The selfembedding need not preserve the chosen enumeration. -/
def IsLabelledBigRamseyBound
    (U : Ordered3Graph Nat) {a : Nat} (A : EnumNode a)
    (t : Nat) : Prop :=
  ∀ (κ : Type) [Fintype κ] [Nonempty κ]
      (χ : GenuineFiniteEmbeddings A U → κ),
    ∃ (w : UnorderedEmbedding U U) (palette : Finset κ),
      palette.card ≤ t ∧
      ∀ v : GenuineFiniteEmbeddings A U,
        χ (v.postcompose w) ∈ palette

/-- The already verified upper theorem gives a genuine palette
of at most N(A) *distinct* colours (list repetitions can only
reduce the cardinality). There is no extra automorphism factor. -/
theorem exactDiaryCount_is_labelledBigRamseyBound
    (G : GenericEnumerated3Graph)
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a) :
    IsLabelledBigRamseyBound U A
      ((∑ P ∈ allIncreasingPresentations A,
          (unmarkedDiariesOfIncreasingPresentation A P).card) *
       Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a)) := by
  classical
  intro κ _ _ χ
  obtain ⟨w, palette, hLength, hCoverage⟩ :=
    actualFiniteAuxRamsey_sharp_upper_on_embeddings_orderedDiarySum
      G U hUniversal A χ
  refine ⟨w, palette.toFinset, ?_, ?_⟩
  · calc
      palette.toFinset.card ≤ palette.length := List.toFinset_card_le palette
      _ = (∑ P ∈ allIncreasingPresentations A,
          (unmarkedDiariesOfIncreasingPresentation A P).card) *
            Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) :=
        hLength
  · intro v
    have h := hCoverage v.val v.property
    change χ (v.postcompose w) ∈ palette at h
    simpa using h

/-- The concrete genuinely unavoidable finite marked-diary
colouring prevents EVERY smaller labelled big Ramsey palette.
We use Option to make the colouring type nonempty even when
the genuine marked-diary subtype has no inhabitant. -/
theorem labelledBigRamseyBound_ge_exactDiaryCount
    (G : GenericEnumerated3Graph)
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    (t : Nat)
    (hBound : IsLabelledBigRamseyBound U A t) :
    (∑ P ∈ allIncreasingPresentations A,
        (unmarkedDiariesOfIncreasingPresentation A P).card) *
      Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) ≤ t := by
  classical
  obtain ⟨χ, hUnavoidable⟩ :=
    exists_unavoidableMarkedDiaryColour_in_universal
      G U hUniversal A
  let χOption : GenuineFiniteEmbeddings A U →
      Option (GenuineMarkedDiaryTypes A) :=
    fun v => some (χ v)
  obtain ⟨w, palette, hCardBound, hCoverage⟩ :=
    hBound (Option (GenuineMarkedDiaryTypes A)) χOption
  have hSomeMem (d : GenuineMarkedDiaryTypes A) :
      (some d : Option (GenuineMarkedDiaryTypes A)) ∈ palette := by
    obtain ⟨v, hv⟩ := hUnavoidable w d
    have hm := hCoverage v
    change some (χ (v.postcompose w)) ∈ palette at hm
    rwa [hv] at hm
  have hSomeImageSub :
      ((Finset.univ : Finset (GenuineMarkedDiaryTypes A)).image
        (fun d => (some d : Option (GenuineMarkedDiaryTypes A)))) ⊆
          palette := by
    intro x hx
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hx
    exact hSomeMem d
  have hSomeInj :
      Function.Injective
        (fun d : GenuineMarkedDiaryTypes A =>
          (some d : Option (GenuineMarkedDiaryTypes A))) := by
    intro x y hxy
    exact Option.some.inj hxy
  have hCardMarked :
      (allGenuineMarkedDiaryFinset A).card ≤ palette.card := by
    calc
      (allGenuineMarkedDiaryFinset A).card =
          (Finset.univ : Finset (GenuineMarkedDiaryTypes A)).card := by
        simp [GenuineMarkedDiaryTypes]
      _ = ((Finset.univ : Finset (GenuineMarkedDiaryTypes A)).image
          (fun d => (some d : Option (GenuineMarkedDiaryTypes A)))).card := by
        exact (Finset.card_image_of_injective _ hSomeInj).symm
      _ ≤ palette.card := Finset.card_le_card hSomeImageSub
  have hExactCount :
      (allGenuineMarkedDiaryFinset A).card =
        (∑ P ∈ allIncreasingPresentations A,
          (unmarkedDiariesOfIncreasingPresentation A P).card) *
            Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) := by
    calc
      (allGenuineMarkedDiaryFinset A).card =
          allGenuineMarkedDiaryCount A :=
        allGenuineMarkedDiaryFinset_card_eq_length A
      _ = (∑ P ∈ allIncreasingPresentations A,
            (unmarkedDiariesOfIncreasingPresentation A P).card) *
          Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) :=
        markedDiaryCount_eq_orderedDiarySum_mul_aut A
  rw [← hExactCount]
  exact hCardMarked.trans hCardBound

/-- Exact *numerical characterisation* of all labelled big Ramsey
bounds for arbitrary countably universal U. The minimal possible
bound is literally the all-presentations diary sum times Aut(A),
with no additional geometric hypotheses beyond an enumerated
generic G (whose existence is a separate model construction). -/
theorem labelledBigRamseyBound_iff_exactDiaryCount_le
    (G : GenericEnumerated3Graph)
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    (t : Nat) :
    IsLabelledBigRamseyBound U A t ↔
      (∑ P ∈ allIncreasingPresentations A,
        (unmarkedDiariesOfIncreasingPresentation A P).card) *
        Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) ≤ t := by
  constructor
  · exact labelledBigRamseyBound_ge_exactDiaryCount
      G U hUniversal A t
  · intro ht
    have hExact := exactDiaryCount_is_labelledBigRamseyBound
      G U hUniversal A
    intro κ _ _ χ
    obtain ⟨w, palette, hCard, hCoverage⟩ := hExact κ χ
    exact ⟨w, palette, hCard.trans ht, hCoverage⟩

end ATRFiniteDecoder
end ThreeUniformDiaries
