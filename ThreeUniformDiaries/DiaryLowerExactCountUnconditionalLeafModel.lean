import ThreeUniformDiaries.DiaryLowerCanonicalColourUnavoidability
import ThreeUniformDiaries.DiaryExistenceCountableLeafOrderEquiv

/-!
# Track C lower: eliminate the chosen leaf model and export exact lower count

The checked countable full-diary existence theorem identifies ANY
enumerated U with all genuine leaves of some full RoleDiary K.
This creates the required actual unordered induced leaf embedding,
with no new genericity, Ramsey or countable unavoidability assumption.

Combined with merged Track C canonical marked-colour unavoidability,
the verified exact finite counting identity gives the full lower
palette inequality in the counting convention of ALL increasing
presentations of an unordered A, with |Aut(A)| multiplied ONCE.

An enumerated generic G remains an explicit parameter only because
its existence is a separate Track A endpoint (#1096). The stronger
countable-source diary-unavoidability theorem of the manuscript is
NOT assumed. The actual numerical BigRamseyDegree definition and
terminal upper/lower equality are separate packaging obligations.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open _root_.ThreeUniformDiaries.Ordered3Graph
open DiaryLeafPriority

/-- Every countably universal unordered 3-hypergraph admits ONE
total, genuinely unavoidable marked finite diary colouring of its
ACTUAL labelled A-embeddings. The full diary model is now a proved
existential choice, not an input hypothesis. -/
theorem exists_unavoidableMarkedDiaryColour_in_universal
    (G : GenericEnumerated3Graph)
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a) :
    ∃ χ : GenuineFiniteEmbeddings A U → GenuineMarkedDiaryTypes A,
      IsEveryMarkedDiaryColourUnavoidable A U χ := by
  classical
  obtain ⟨K, e, DK, hOrder, hEdge⟩ :=
    exists_countable_diary_order_equiv_leaf_reduct U
  let F : UnorderedEmbedding U K := {
    toFun := fun x => (e x).val
    injective := by
      intro x y hxy
      apply e.injective
      apply Subtype.ext
      exact hxy
    edge_iff := by
      intro x y z hxy hyz
      have hxyK : (e x).val < (e y).val :=
        (hOrder x y).mp hxy
      have hyzK : (e y).val < (e z).val :=
        (hOrder y z).mp hyz
      calc
        U.unorderedEdge x y z ↔ U.edge x y z :=
          U.unorderedEdge_iff_of_lt x y z hxy hyz
        _ ↔ K.edge (e x).val (e y).val (e z).val :=
          (hEdge x y z hxy hyz).symm
        _ ↔ K.unorderedEdge (e x).val (e y).val (e z).val :=
          (K.unorderedEdge_iff_of_lt
            (e x).val (e y).val (e z).val hxyK hyzK).symm
  }
  have hFLeaf : ∀ u : Nat, IsLeaf K (F u) := by
    intro u
    exact (e u).property
  refine ⟨canonicalMarkedDiaryColour DK F hFLeaf A, ?_⟩
  exact canonicalMarkedDiaryColour_unavoidable
    G U K hUniversal DK F hFLeaf A

/-- Exact finite big-Ramsey LOWER palette for a fixed finite
unordered A, counted over every increasing presentation and with
the labelled automorphism factor exactly once. For the one
concrete unavoidable colouring produced above, every ambient
induced self-copy still sees at least this many distinct colours.

No conditional hUnavoidable input remains in the statement.
The only generic-model input G is a separate existence issue,
and no countable diary-unavoidability assertion is used. -/
theorem universal_exactMarkedDiary_lower_palette
    (G : GenericEnumerated3Graph)
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a) :
    ∃ χ : GenuineFiniteEmbeddings A U → GenuineMarkedDiaryTypes A,
      ∀ (w : UnorderedEmbedding U U)
        (palette : Finset (GenuineMarkedDiaryTypes A)),
        (∀ v : GenuineFiniteEmbeddings A U,
          χ (v.postcompose w) ∈ palette) →
        (∑ P ∈ allIncreasingPresentations A,
            (unmarkedDiariesOfIncreasingPresentation A P).card) *
          Fintype.card
            (FiniteHypergraphAut A.toOrdered3Graph a) ≤
              palette.card := by
  classical
  obtain ⟨χ, hUnavoidable⟩ :=
    exists_unavoidableMarkedDiaryColour_in_universal
      G U hUniversal A
  refine ⟨χ, ?_⟩
  intro w palette hPalette
  exact unavoidableMarkedDiaryColours_orderedDiarySum_lower
    A U χ hUnavoidable w palette hPalette

end ATRFiniteDecoder
end ThreeUniformDiaries
