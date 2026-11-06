import ThreeUniformDiaries.DiaryUnmarkedFullDiaryCharacterisation

/-!
# Track A/C: the diary count depends only on the UNORDERED A

The manuscript first defines a diary of an ORDERED finite A, then
states the big Ramsey degree for an UNORDERED finite A. The verified
exact degree counts genuine full finite diaries over ALL increasing
presentations of A, but it is also useful to verify that the
canonical unmarked source family does not depend on the arbitrary
choice of the original EnumNode a presentation.

We prove a stronger *literal finite family equality*. If two
EnumNode presentations A and B differ by any permutation of their
underlying finite vertices preserving and reflecting EVERY unordered
hyperedge/nonedge, then the predicate
IsFiniteFullDiaryOfUnordered A S is equivalent to
IsFiniteFullDiaryOfUnordered B S for every genuine finite source S.
The permutation witnessing an increasing presentation composes with
the original isomorphism. The already verified two-way finite diary
classification then gives equality of the actual deduplicated
Finsets allGenuineUnmarkedDiarySources A and B, not just equality
of their cardinalities.

The proof does not use a countable Ramsey theorem, a generic
hypergraph, any infinite diary, or countable unavoidability.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- An induced isomorphism of the underlying UNORDERED finite
hypergraphs, expressed as a permutation of their common Fin a
vertex set. The target label order is completely unrestricted. -/
def IsUnorderedRelabelling
    {a : Nat} (A B : EnumNode a)
    (τ : Equiv.Perm (Fin a)) : Prop :=
  ∀ i j k : Fin a,
    A.toOrdered3Graph.unorderedEdge i.val j.val k.val ↔
      B.toOrdered3Graph.unorderedEdge
        (τ i).val (τ j).val (τ k).val

/-- The actual full V/E/S finite diary predicate of UNORDERED A
is invariant under arbitrary induced relabelling of A's vertices,
including repeated and permuted triples. -/
theorem finiteFullDiaryOfUnordered_iff_of_relabelling
    {a : Nat} (A B : EnumNode a)
    (τ : Equiv.Perm (Fin a))
    (hIso : IsUnorderedRelabelling A B τ)
    (S : ProtectedSource 0) :
    IsFiniteFullDiaryOfUnordered A S ↔
      IsFiniteFullDiaryOfUnordered B S := by
  classical
  constructor
  · rintro ⟨hFull, hCard, σ, hEdges⟩
    refine ⟨hFull, hCard, τ.symm.trans σ, ?_⟩
    intro i j k
    have hBackward :
        B.toOrdered3Graph.unorderedEdge i.val j.val k.val ↔
          A.toOrdered3Graph.unorderedEdge
            (τ.symm i).val (τ.symm j).val (τ.symm k).val := by
      simpa only [Equiv.apply_symm_apply] using
        (hIso (τ.symm i) (τ.symm j) (τ.symm k)).symm
    change B.toOrdered3Graph.unorderedEdge i.val j.val k.val ↔
      S.picture.toOrdered3Graph.unorderedEdge
        (((S.leafPositions.orderIsoOfFin hCard)
          (σ (τ.symm i))).val).val
        (((S.leafPositions.orderIsoOfFin hCard)
          (σ (τ.symm j))).val).val
        (((S.leafPositions.orderIsoOfFin hCard)
          (σ (τ.symm k))).val).val
    exact hBackward.trans
      (hEdges (τ.symm i) (τ.symm j) (τ.symm k))
  · rintro ⟨hFull, hCard, σ, hEdges⟩
    refine ⟨hFull, hCard, τ.trans σ, ?_⟩
    intro i j k
    change A.toOrdered3Graph.unorderedEdge i.val j.val k.val ↔
      S.picture.toOrdered3Graph.unorderedEdge
        (((S.leafPositions.orderIsoOfFin hCard)
          (σ (τ i))).val).val
        (((S.leafPositions.orderIsoOfFin hCard)
          (σ (τ j))).val).val
        (((S.leafPositions.orderIsoOfFin hCard)
          (σ (τ k))).val).val
    exact (hIso i j k).trans (hEdges (τ i) (τ j) (τ k))

/-- Stronger than cardinal invariance: the FULL DEDUPLICATED
genuine unmarked diary source family is literally equal for
any two finite presentations of the same unordered A. -/
theorem allGenuineUnmarkedDiarySources_eq_of_relabelling
    {a : Nat} (A B : EnumNode a)
    (τ : Equiv.Perm (Fin a))
    (hIso : IsUnorderedRelabelling A B τ) :
    allGenuineUnmarkedDiarySources A =
      allGenuineUnmarkedDiarySources B := by
  classical
  apply Finset.ext
  intro S
  exact
    (mem_allGenuineUnmarkedDiarySources_iff_fullDiaryOfUnordered A S).trans
      ((finiteFullDiaryOfUnordered_iff_of_relabelling A B τ hIso S).trans
        (mem_allGenuineUnmarkedDiarySources_iff_fullDiaryOfUnordered B S).symm)

/-- Consequently the cardinal used in the SHARP unlabelled
copy-colouring upper degree is independent of the original
vertex enumeration of finite A. -/
theorem genuineUnmarkedDiaryCount_eq_of_relabelling
    {a : Nat} (A B : EnumNode a)
    (τ : Equiv.Perm (Fin a))
    (hIso : IsUnorderedRelabelling A B τ) :
    (allGenuineUnmarkedDiarySources A).card =
      (allGenuineUnmarkedDiarySources B).card := by
  rw [allGenuineUnmarkedDiarySources_eq_of_relabelling A B τ hIso]

end ATRFiniteDecoder
end ThreeUniformDiaries
