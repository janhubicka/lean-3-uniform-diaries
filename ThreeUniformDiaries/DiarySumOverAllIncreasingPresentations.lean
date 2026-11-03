import ThreeUniformDiaries.DiaryUnmarkedFullDiaryCharacterisation

/-!
# Track C: diary counts summed over ALL increasing presentations of A

The manuscript states the big Ramsey degree for an UNORDERED finite
hypergraph A, but earlier defines a diary "of A" only when A is
ORDERED. A single arbitrarily selected enumeration can miss
genuinely different ordered presentations of the same unordered A.

We define all ordered presentations as the finite subset of
EnumNode a obtained by permuting the labels of A. This definition
uses literal induced hyperedge AND nonedge reflection on every
increasing triple, so distinct ordered tables are not collapsed.

Every counted unmarked full finite diary S has EXACTLY a genuine
leaves by the verified Track C classification. Its literal canonical
increasing leaf EnumNode gives one of these ordered presentations.
Group unmarked diaries by that canonical table and apply finite
fibrewise counting. Unrealised ordered presentations contribute ZERO.

As a corollary the already verified marked count is the sum of
the diary numbers for ALL increasing presentations, multiplied
by |Aut(A)| exactly ONCE. No arbitrary enumeration and no extra
marking factor is assumed. This is an EXACT finite counting
identity, not a proof of the matching infinite lower bound.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- A genuine INCREASING ordered presentation P of the underlying
UNORDERED finite A. An explicit permutation σ sends each original
label to its new rank, and its inverse recovers the old label at
each increasing position. Both edges and nonedges are reflected. -/
def IsIncreasingPresentationOf
    {a : Nat} (A P : EnumNode a) : Prop :=
  ∃ σ : Equiv.Perm (Fin a),
    ∀ i j k : Fin a, i < j → j < k →
      (P.toOrdered3Graph.edge i.val j.val k.val ↔
        A.toOrdered3Graph.unorderedEdge
          (σ.symm i).val (σ.symm j).val (σ.symm k).val)

/-- The finite, deduplicated universe of ALL different increasing
ordered presentations of the given underlying unordered A. -/
noncomputable def allIncreasingPresentations
    {a : Nat} (A : EnumNode a) : Finset (EnumNode a) := by
  classical
  exact (Finset.univ : Finset (EnumNode a)).filter
    (IsIncreasingPresentationOf A)

/-- Presentation membership is the actual permutation condition,
not a choice of one particular labelled ordering. -/
theorem mem_allIncreasingPresentations_iff
    {a : Nat} (A P : EnumNode a) :
    P ∈ allIncreasingPresentations A ↔
      IsIncreasingPresentationOf A P := by
  classical
  simp [allIncreasingPresentations]

/-- The canonical ordered presentation determined by an actual
unmarked finite diary S in U_A. Its leaf-count equality follows
from family membership and does not need a supplied marking. -/
noncomputable def unmarkedDiaryOrderedLeafEnum
    {a : Nat} (A : EnumNode a)
    (S : ↑(allGenuineUnmarkedDiarySources A)) : EnumNode a :=
  S.val.increasingLeafEnum a
    (allGenuineUnmarkedDiarySources_leaf_card A S.val S.property)

/-- Every unmarked diary in the verified family has a canonical
ordered leaf presentation that genuinely belongs to the ENTIRE
finite set of increasing presentations of unordered A. -/
theorem unmarkedDiaryOrderedLeafEnum_isPresentation
    {a : Nat} (A : EnumNode a)
    (S : ↑(allGenuineUnmarkedDiarySources A)) :
    IsIncreasingPresentationOf A
      (unmarkedDiaryOrderedLeafEnum A S) := by
  classical
  obtain ⟨hCard, σ, hEdge⟩ :=
    allGenuineUnmarkedDiarySources_has_increasingPresentation
      A S.val S.property
  refine ⟨σ, ?_⟩
  intro i j k hij hjk
  simpa only [unmarkedDiaryOrderedLeafEnum] using
    (hEdge i j k hij hjk)

/-- The finite diaries of this PARTICULAR increasing
presentation P, with their counted unmarked identity retained.
In contrast to a marked palette this is NOT multiplied by
automorphisms; each source has just one literal leaf table. -/
noncomputable def unmarkedDiariesOfIncreasingPresentation
    {a : Nat} (A P : EnumNode a) :
    Finset (↑(allGenuineUnmarkedDiarySources A)) := by
  classical
  exact (Finset.univ :
      Finset (↑(allGenuineUnmarkedDiarySources A))).filter
    (fun S => unmarkedDiaryOrderedLeafEnum A S = P)

/-- Exact sum over ALL increasing presentations of unordered A.
Those with no full finite diary shape automatically contribute 0;
the theorem does not require their realisability or assume the
summands are equal. -/
theorem unmarkedDiaryCount_eq_sum_allIncreasingPresentations
    {a : Nat} (A : EnumNode a) :
    (allGenuineUnmarkedDiarySources A).card =
      ∑ P ∈ allIncreasingPresentations A,
        (unmarkedDiariesOfIncreasingPresentation A P).card := by
  classical
  let U := allGenuineUnmarkedDiarySources A
  have hMaps :
      ((Finset.univ : Finset (↑U)) : Set (↑U)).MapsTo
        (fun S : ↑U => unmarkedDiaryOrderedLeafEnum A S)
        (allIncreasingPresentations A : Set (EnumNode a)) := by
    intro S _
    exact (mem_allIncreasingPresentations_iff A
      (unmarkedDiaryOrderedLeafEnum A S)).mpr
      (unmarkedDiaryOrderedLeafEnum_isPresentation A S)
  have hSum :=
    Finset.card_eq_sum_card_fiberwise
      (f := fun S : ↑U => unmarkedDiaryOrderedLeafEnum A S)
      (s := (Finset.univ : Finset (↑U)))
      (t := allIncreasingPresentations A) hMaps
  calc
    U.card = (Finset.univ : Finset (↑U)).card := by simp
    _ = ∑ P ∈ allIncreasingPresentations A,
        ((Finset.univ : Finset (↑U)).filter
          (fun S => unmarkedDiaryOrderedLeafEnum A S = P)).card :=
      hSum
    _ = ∑ P ∈ allIncreasingPresentations A,
        (unmarkedDiariesOfIncreasingPresentation A P).card := rfl

/-- Final finite counting identity in the exact form needed
for an unordered source A: sum full-diary counts over EVERY
increasing ordered presentation, then multiply by |Aut(A)| once.

This is a counting statement. The upper-bound Ramsey theorem
is independently checked; the exact big Ramsey degree still
requires the matching countable-source lower bound. -/
theorem markedDiaryCount_eq_orderedDiarySum_mul_aut
    {a : Nat} (A : EnumNode a) :
    allGenuineMarkedDiaryCount A =
      (∑ P ∈ allIncreasingPresentations A,
        (unmarkedDiariesOfIncreasingPresentation A P).card) *
        Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) := by
  rw [allGenuineMarkedDiaryCount_eq_unmarked_mul_aut A,
    unmarkedDiaryCount_eq_sum_allIncreasingPresentations A]

end ATRFiniteDecoder
end ThreeUniformDiaries
