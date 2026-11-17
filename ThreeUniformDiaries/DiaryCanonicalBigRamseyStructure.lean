import ThreeUniformDiaries.CoherentSharpColoursBRSCountableLanguage
import ThreeUniformDiaries.DiaryCanonicalMarkedRestrictionFunctorial
import ThreeUniformDiaries.DiaryExactLabelledBigRamseyDegreeNoGeneric
import ThreeUniformDiaries.DiaryMarkedUnmarkedGlobalCount
import ThreeUniformDiaries.DiarySumOverAllIncreasingPresentations
import ThreeUniformDiaries.DiaryExistenceCountableLeafOrderEquiv
import ThreeUniformDiaries.DiaryGenericExistenceByPairCode

/-!
# A concrete sharp unavoidable big Ramsey expansion of 3-hypergraphs

Given a genuinely full countable RoleDiary K and an induced unordered
leaf embedding U -> K, use the kernel-verified finite canonical
marked-diary colours to build a COHERENT finite colour system.
All finite palette colours are unavoidable in any U-selfcopy, and
the exact restriction identity under arbitrary finite embeddings
was checked independently.

The abstract relational profile assembly gives:
* a COUNTABLE arity-indexed relational expansion language,
* a bijection from each finite marked-diary palette onto the
  realized full induced expansion types for A,
* every expansion type unavoidable in every induced U-selfcopy,
* the sharp labelled BRD cardinality of expansion types.

Finally, the existing full countable diary leaf-reduct theorem
supplies K and its leaf isomorphism for EVERY countably universal
unordered 3-hypergraph U. No original countable diary Ramsey
theorem, countable-source diary-unavoidability, or fusion hypothesis
is used by this construction.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open _root_.ThreeUniformDiaries.Ordered3Graph
open DiaryLeafPriority

/-- The verified canonical marked colours, as an actual finite
coherent relational colour system over one chosen full diary
leaf model. -/
noncomputable def canonicalMarkedColourSystem
    (G : GenericEnumerated3Graph)
    (U K : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    (DK : RoleDiary K)
    (F : UnorderedEmbedding U K)
    (hFLeaf : ∀ x : Nat, IsLeaf K (F x)) :
    CoherentFiniteColourSystem U := by
  classical
  refine {
    Palette := fun _ A => GenuineMarkedDiaryTypes A
    finitePalette := ?_
    colour := ?_
    surj := ?_
    coherent := ?_
    unavoidable := ?_
  }
  · intro n A
    infer_instance
  · intro n A v
    exact canonicalMarkedDiaryColour DK F hFLeaf A v
  · intro n A
    exact canonicalMarkedDiaryColour_surjective
      G U K hUniversal DK F hFLeaf A
  · intro a b A B i hi v w hSame
    exact canonicalMarkedDiaryColour_restrict_fibre
      DK F hFLeaf A B i hi v w hSame
  · intro n A w d
    exact (canonicalMarkedDiaryColour_unavoidable
      G U K hUniversal DK F hFLeaf A) w d

/-- The finite palette of genuine marked A-diary colours
is EXACTLY the labelled BRD number: sum of genuine unmarked
diaries over all increasing presentations, times |Aut(A)| once. -/
theorem genuineMarkedPalette_card_exact
    {a : Nat} (A : EnumNode a) :
    Fintype.card (GenuineMarkedDiaryTypes A) =
      (∑ P ∈ allIncreasingPresentations A,
          (unmarkedDiariesOfIncreasingPresentation A P).card) *
        Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) := by
  classical
  have hc := allGenuineMarkedFinset_card_eq_unmarked_mul_aut A
  rw [unmarkedDiaryCount_eq_sum_allIncreasingPresentations A] at hc
  simpa [GenuineMarkedDiaryTypes] using hc

/-- COMPLETE full finite induced expansion types of A are
counted sharply by its labelled big Ramsey degree. This theorem
is about ALL arity-indexed relation symbols, not just the
top-colour predicate. -/
theorem canonicalMarkedExpansionTypes_card
    (G : GenericEnumerated3Graph)
    (U K : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    (DK : RoleDiary K)
    (F : UnorderedEmbedding U K)
    (hFLeaf : ∀ x : Nat, IsLeaf K (F x))
    {a : Nat} (A : EnumNode a) :
    let C := canonicalMarkedColourSystem
      G U K hUniversal DK F hFLeaf
    Fintype.card (C.RealizedProfile A) =
      (∑ P ∈ allIncreasingPresentations A,
          (unmarkedDiariesOfIncreasingPresentation A P).card) *
        Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) := by
  classical
  let C := canonicalMarkedColourSystem
    G U K hUniversal DK F hFLeaf
  change Fintype.card (C.RealizedProfile A) = _
  calc
    Fintype.card (C.RealizedProfile A) =
        Fintype.card (C.Palette a A) :=
      C.realizedProfile_card A
    _ = (∑ P ∈ allIncreasingPresentations A,
          (unmarkedDiariesOfIncreasingPresentation A P).card) *
        Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) := by
          simpa only [C, canonicalMarkedColourSystem] using
            genuineMarkedPalette_card_exact A

/-- This explicitly constructed expansion is sharp relative to
the verified ordinary finite-colouring labelled BRD definition. -/
theorem canonicalMarkedExpansionTypes_sharp_iff
    (G : GenericEnumerated3Graph)
    (U K : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    (DK : RoleDiary K)
    (F : UnorderedEmbedding U K)
    (hFLeaf : ∀ x : Nat, IsLeaf K (F x))
    {a : Nat} (A : EnumNode a) (t : Nat) :
    let C := canonicalMarkedColourSystem
      G U K hUniversal DK F hFLeaf
    IsLabelledBigRamseyBound U A t ↔
      Fintype.card (C.RealizedProfile A) ≤ t := by
  have hCount :=
    canonicalMarkedExpansionTypes_card G U K hUniversal DK F hFLeaf A
  change IsLabelledBigRamseyBound U A t ↔
    Fintype.card
      ((canonicalMarkedColourSystem G U K hUniversal DK F hFLeaf).RealizedProfile A)
        ≤ t
  rw [hCount]
  exact labelledBigRamseyBound_iff_exactDiaryCount_le_noGeneric
    U hUniversal A t

/-- Every countably universal unordered 3-hypergraph has a
COUNTABLE relational expansion whose exact realized finite
expansion types are the numerical labelled BRDs, and EVERY
type survives inside every reduct selfcopy.

This is the formal BRS defining property, expressed using the
explicit arity-indexed family of additional relation symbols
rather than a separately introduced model-theory language API. -/
theorem exists_canonical_marked_bigRamsey_expansion
    (U : Ordered3Graph Nat) (hUniversal : CountablyUniversal U) :
    ∃ C : CoherentFiniteColourSystem U,
      Countable C.RelationSymbol ∧
      (∀ {a : Nat} (A : EnumNode a),
        Fintype.card (C.RealizedProfile A) =
          (∑ P ∈ allIncreasingPresentations A,
              (unmarkedDiariesOfIncreasingPresentation A P).card) *
            Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a)) ∧
      (∀ {a : Nat} (A : EnumNode a)
        (p : C.RealizedProfile A) (w : UnorderedEmbedding U U),
        ∃ v : GenuineFiniteEmbeddings A U,
          C.inducedProfile A (v.postcompose w) = p.val) := by
  classical
  let G : GenericEnumerated3Graph := canonicalGenericEnumerated3Graph
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
  have hFLeaf : ∀ x : Nat, IsLeaf K (F x) :=
    fun x => (e x).property
  let C := canonicalMarkedColourSystem G U K hUniversal DK F hFLeaf
  refine ⟨C, inferInstance, ?_, ?_⟩
  · intro a A
    exact canonicalMarkedExpansionTypes_card
      G U K hUniversal DK F hFLeaf A
  · intro a A p w
    exact C.realizedProfile_unavoidable A p w

end ATRFiniteDecoder
end ThreeUniformDiaries
