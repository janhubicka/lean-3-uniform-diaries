import ThreeUniformDiaries.DiaryUpperBoundByOrderedDiarySum
import ThreeUniformDiaries.DiarySharpUpperOnEmbeddings

/-!
# Track C lower-colour-count bridge: exact unavoidable finite diary palette

The verified finite diary count is the sum of the numbers of full
finite diaries over ALL increasing presentations of unordered A,
times |Aut(A)| once. The unconditional sharp UPPER palette of
exactly this size is already checked.

For the LOWER bound, the mathematical task is to construct ONE
canonical colouring of genuine labelled A-embeddings by the actual
finite marked diary source they generate, and then prove EVERY
marked source occurs in the image of EVERY ambient self-copy.

This module isolates that last quantified finite-colouring
statement. Given an actual marked-diary-valued colouring and
a genuine `hUnavoidable` hypothesis saying every colour occurs
inside every self-copy, no smaller palette can suffice.

This is a finite cardinal/counting implication; it DOES NOT
assert the existence of the persistent canonical colouring or
any nontrivial countable unavoidability theorem. Such a colour
must be built from the sorted finite diary support and the
marked-rank/source-EnumNode transport of Track C PRs #1073/#1078.

In particular there is no circular use of the desired full
big Ramsey degree lower bound as a proof of hUnavoidable.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- Type of all genuine *labelled induced* embeddings of finite A
in the countable unordered target U. The bound and unavoidability
are stated on actual embeddings, not all maps Fin a -> Nat. -/
abbrev GenuineFiniteEmbeddings
    {a : Nat} (A : EnumNode a) (U : Ordered3Graph Nat) : Type :=
  {v : Fin a → Nat // IsInducedLabelledCopy A U v}

/-- The canonical finite palette of ACTUAL marked full diary
source types of A, with the exact closed finite universe already
verified by Track C. No separate fake shape index is introduced. -/
abbrev GenuineMarkedDiaryTypes
    {a : Nat} (A : EnumNode a) : Type :=
  ↑(allGenuineMarkedDiaryFinset A)

/-- Actual self-copying of an induced labelled embedding,
including proof of preservation of inducedness under unordered
self-embeddings of U. -/
def GenuineFiniteEmbeddings.postcompose
    {a : Nat} {A : EnumNode a} {U : Ordered3Graph Nat}
    (v : GenuineFiniteEmbeddings A U)
    (w : UnorderedEmbedding U U) :
    GenuineFiniteEmbeddings A U :=
  ⟨fun i => w (v.val i),
    isInducedLabelledCopy_map_unordered A w v.val v.property⟩

/-- Every finite marked diary colour occurs in the image of
every ambient self-copy: a precise, independently testable
predicate on a concrete colouring, NOT a Ramsey conclusion. -/
def IsEveryMarkedDiaryColourUnavoidable
    {a : Nat} (A : EnumNode a) (U : Ordered3Graph Nat)
    (χ : GenuineFiniteEmbeddings A U → GenuineMarkedDiaryTypes A) :
    Prop :=
  ∀ w : UnorderedEmbedding U U,
    ∀ d : GenuineMarkedDiaryTypes A,
      ∃ v : GenuineFiniteEmbeddings A U,
        χ (v.postcompose w) = d

/-- If a genuine marked-diary colouring attains EVERY genuine
finite diary type within every ambient induced self-copy, then
any palette covering ALL A-embeddings in that copy has at least
the exact size of the marked diary family. No degree terminology
or hidden lower-bound premise is needed. -/
theorem unavoidableMarkedDiaryColours_palette_card_ge
    {a : Nat} (A : EnumNode a) (U : Ordered3Graph Nat)
    (χ : GenuineFiniteEmbeddings A U → GenuineMarkedDiaryTypes A)
    (hUnavoidable : IsEveryMarkedDiaryColourUnavoidable A U χ)
    (w : UnorderedEmbedding U U)
    (palette : Finset (GenuineMarkedDiaryTypes A))
    (hPalette : ∀ v : GenuineFiniteEmbeddings A U,
      χ (v.postcompose w) ∈ palette) :
    (allGenuineMarkedDiaryFinset A).card ≤ palette.card := by
  classical
  have hAll :
      (Finset.univ : Finset (GenuineMarkedDiaryTypes A)) ⊆
        palette := by
    intro d _
    obtain ⟨v, hv⟩ := hUnavoidable w d
    rw [← hv]
    exact hPalette v
  have hCard := Finset.card_le_card hAll
  simpa using hCard

/-- The exact lower number dictated by the FINITE diary
classification is the sum over ALL increasing presentations
of unordered A, multiplied by the true finite automorphism
group cardinal ONCE.

This conclusion is conditional only on a concrete colouring
whose every marked diary colour is unavoidable; existence
of that colouring is a separate geometric theorem, not an
assumption automatically supplied by the upper bound. -/
theorem unavoidableMarkedDiaryColours_orderedDiarySum_lower
    {a : Nat} (A : EnumNode a) (U : Ordered3Graph Nat)
    (χ : GenuineFiniteEmbeddings A U → GenuineMarkedDiaryTypes A)
    (hUnavoidable : IsEveryMarkedDiaryColourUnavoidable A U χ)
    (w : UnorderedEmbedding U U)
    (palette : Finset (GenuineMarkedDiaryTypes A))
    (hPalette : ∀ v : GenuineFiniteEmbeddings A U,
      χ (v.postcompose w) ∈ palette) :
    (∑ P ∈ allIncreasingPresentations A,
      (unmarkedDiariesOfIncreasingPresentation A P).card) *
      Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) ≤
        palette.card := by
  calc
    (∑ P ∈ allIncreasingPresentations A,
        (unmarkedDiariesOfIncreasingPresentation A P).card) *
        Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) =
      allGenuineMarkedDiaryCount A :=
        (markedDiaryCount_eq_orderedDiarySum_mul_aut A).symm
    _ = (allGenuineMarkedDiaryFinset A).card :=
        (allGenuineMarkedDiaryFinset_card_eq_length A).symm
    _ ≤ palette.card :=
      unavoidableMarkedDiaryColours_palette_card_ge
        A U χ hUnavoidable w palette hPalette

end ATRFiniteDecoder
end ThreeUniformDiaries
