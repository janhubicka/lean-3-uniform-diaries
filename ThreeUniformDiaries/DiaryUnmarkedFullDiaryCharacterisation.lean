import ThreeUniformDiaries.DiaryUnmarkedSourceOrderedPresentation

/-!
# Track C: exact membership test for diaries of an unordered hypergraph

The finite genuine unmarked diary family was initially defined by
forgetting the COMPLETE marking in a deduplicated finite family.
The manuscript, by contrast, calls a diary "of ordered P" when its
genuine leaves, enumerated increasingly, are isomorphic to P.

We bridge these two definitions in BOTH directions.

An unmarked finite source S belongs to the genuine family for
an unordered finite A if and only if:
* S is a full finite V/E/S diary on its actual finite frame;
* the full genuine leaf set has precisely a=|A| vertices; and
* its increasing leaf enumeration has the complete induced
  unordered A edge table, after a permutation of the A labels.

The reverse direction is nontrivial: a given permutation of an
ordered leaf presentation reconstructs an injective exhaustive
marking of A by actual genuine source leaves. There are NO
additional markings or source-code assumptions.

This settles the finite source-classification *definition* and
does NOT establish the matching countable unavoidability/lower
big Ramsey bound. Neither the final Ramsey theorem nor any
generic embedding appears in these proofs.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- A finite full diary whose INCREASING leaf reduct is some
ordered presentation of the given UNORDERED A.

The permutation is an explicit datum describing which abstract
A-label occupies each increasing source leaf position. Requiring
all unordered triples includes complete induced nonedge reflection,
not merely homomorphic edge preservation. -/
def IsFiniteFullDiaryOfUnordered
    {a : Nat} (A : EnumNode a)
    (S : ProtectedSource 0) : Prop :=
  ∃ (_hFull : FiniteRoleDiaryBlock
        S.picture.toOrdered3Graph (S.k + 1))
    (hCard : S.leafPositions.card = a)
    (σ : Equiv.Perm (Fin a)),
    ∀ i j k : Fin a,
      A.toOrdered3Graph.unorderedEdge i.val j.val k.val ↔
      S.picture.toOrdered3Graph.unorderedEdge
        (((S.leafPositions.orderIsoOfFin hCard) (σ i)).val).val
        (((S.leafPositions.orderIsoOfFin hCard) (σ j)).val).val
        (((S.leafPositions.orderIsoOfFin hCard) (σ k)).val).val

/-- Exact equivalence of the two notions of an unmarked diary
"of unordered A": the deduplicated finite-source family and
the original role-based full diary whose increasing leaf reduct
is a permutation presentation of A. There are no hidden extra
leaf markings in the RHS predicate. -/
theorem mem_allGenuineUnmarkedDiarySources_iff_fullDiaryOfUnordered
    {a : Nat} (A : EnumNode a)
    (S : ProtectedSource 0) :
    S ∈ allGenuineUnmarkedDiarySources A ↔
      IsFiniteFullDiaryOfUnordered A S := by
  classical
  constructor
  · intro hS
    let p : GenuineDiaryMarkingFibre A S :=
      Classical.choice
        ((mem_allGenuineUnmarkedDiarySources_iff A S).mp hS)
    let T : MarkedFiniteSource 0 a := ⟨S, p.val⟩
    have hShape : IsGenuineMarkedDiaryShape A T := p.property
    let hCard : S.leafPositions.card = a :=
      genuineMarkedDiaryShape_leafPositions_card A T hShape
    let σ : Equiv.Perm (Fin a) :=
      genuineMarkedDiaryShape_labelRankPerm A T hShape
    refine ⟨hShape.1, hCard, σ, ?_⟩
    intro i j k
    exact genuineMarkedDiaryShape_labelRank_edge_iff
      A T hShape i j k
  · rintro ⟨hDiary, hCard, σ, hEdges⟩
    let E : Fin a ≃o ↑S.leafPositions :=
      S.leafPositions.orderIsoOfFin hCard
    let mark : Fin a → Fin (S.k + 1) :=
      fun i => (E (σ i)).val
    have hInject : Function.Injective
        (fun i : Fin a => (mark i).val) := by
      intro i j heq
      apply σ.injective
      apply E.injective
      apply Subtype.ext
      apply Fin.ext
      exact heq
    have hCopy :
        IsFiniteLabelledCopy
          A.toOrdered3Graph S.picture.toOrdered3Graph a
          (fun i => (mark i).val) := by
      refine ⟨hInject, ?_⟩
      intro i j k
      exact hEdges i j k
    have hMarkedLeaves :
        ∀ i : Fin a,
          IsLeaf S.picture.toOrdered3Graph (mark i).val := by
      intro i
      have hi : (E (σ i)).val ∈ S.leafPositions :=
        (E (σ i)).property
      simpa only [mark, ProtectedSource.leafPositions,
        Finset.mem_filter, Finset.mem_univ, true_and] using hi
    have hCovered :
        ∀ u : Nat, 3 ≤ u → u < S.k + 1 →
          IsLeaf S.picture.toOrdered3Graph u →
          ∃ i : Fin a, (mark i).val = u := by
      intro u _hu3 hu hLeaf
      let j : Fin (S.k + 1) := ⟨u, hu⟩
      have hj : j ∈ S.leafPositions := by
        simpa only [ProtectedSource.leafPositions,
          Finset.mem_filter, Finset.mem_univ, true_and]
          using hLeaf
      refine ⟨σ.symm (E.symm ⟨j, hj⟩), ?_⟩
      change ((E (σ (σ.symm (E.symm ⟨j, hj⟩)))).val).val = u
      simp [j]
    have hShape :
        IsGenuineMarkedDiaryShape A ⟨S, mark⟩ := by
      change FiniteRoleDiaryBlock
          S.picture.toOrdered3Graph (S.k + 1) ∧
        IsFiniteLabelledCopy
          A.toOrdered3Graph S.picture.toOrdered3Graph a
          (fun i => (mark i).val) ∧
        (∀ i : Fin a,
          IsLeaf S.picture.toOrdered3Graph (mark i).val) ∧
        (∀ u : Nat, 3 ≤ u → u < S.k + 1 →
          IsLeaf S.picture.toOrdered3Graph u →
          ∃ i : Fin a, (mark i).val = u)
      exact ⟨hDiary, hCopy, hMarkedLeaves, hCovered⟩
    exact (mem_allGenuineUnmarkedDiarySources_iff A S).mpr
      ⟨⟨mark, hShape⟩⟩

/-- The exact finite family `U_A` is therefore a finite
enumeration of full diary sources satisfying the manuscript's
role-based V/E/S finite diary axioms and admitting some increasing
presentation of unordered A. No orientation has been chosen
arbitrarily, and there is no second automorphism multiplier. -/
theorem allGenuineUnmarkedDiarySources_fullDiary_iff
    {a : Nat} (A : EnumNode a)
    (S : ProtectedSource 0) :
    IsFiniteFullDiaryOfUnordered A S ↔
      S ∈ allGenuineUnmarkedDiarySources A :=
  (mem_allGenuineUnmarkedDiarySources_iff_fullDiaryOfUnordered A S).symm

end ATRFiniteDecoder
end ThreeUniformDiaries
