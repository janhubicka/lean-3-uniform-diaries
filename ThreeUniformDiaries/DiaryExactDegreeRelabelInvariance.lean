import ThreeUniformDiaries.DiaryUnorderedPresentationRelabelInvariance
import ThreeUniformDiaries.DiarySumOverAllIncreasingPresentations

/-!
# Track A/C: the ENTIRE exact degree is invariant under relabelling A

The counted finite full diary family is literally invariant under
unordered relabelling of a finite EnumNode A (preceding theorem).
The labelled big Ramsey degree additionally contains |Aut(A)|.
We conjugate finite hypergraph automorphisms by a given arbitrary
induced unordered relabelling, with explicit inverses, to prove
that its automorphism group cardinal is also invariant.

The resulting exact all-increasing-presentations sum times
|Aut(A)| is thus independent of the initial EnumNode presentation.
This directly resolves the representation dependence hidden
in the manuscript's phrase "diaries of unordered A", but it
does NOT repair the frozen printed theorem or prove full
countable diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- An unordered isomorphism remains an unordered isomorphism
when its finite vertex permutation is reversed. -/
theorem isUnorderedRelabelling_symm
    {a : Nat} (A B : EnumNode a)
    (τ : Equiv.Perm (Fin a))
    (hIso : IsUnorderedRelabelling A B τ) :
    IsUnorderedRelabelling B A τ.symm := by
  intro i j k
  simpa only [Equiv.apply_symm_apply] using
    (hIso (τ.symm i) (τ.symm j) (τ.symm k)).symm

/-- Conjugation by the underlying unordered isomorphism maps an
actual automorphism of A to an actual automorphism of B. -/
noncomputable def relabelFiniteHypergraphAut
    {a : Nat} (A B : EnumNode a)
    (τ : Equiv.Perm (Fin a))
    (hIso : IsUnorderedRelabelling A B τ)
    (σ : FiniteHypergraphAut A.toOrdered3Graph a) :
    FiniteHypergraphAut B.toOrdered3Graph a := by
  let p : Equiv.Perm (Fin a) := (τ.symm.trans σ.val).trans τ
  refine ⟨p, ?_⟩
  intro i j k
  change B.toOrdered3Graph.unorderedEdge i.val j.val k.val ↔
    B.toOrdered3Graph.unorderedEdge
      (τ (σ.val (τ.symm i))).val
      (τ (σ.val (τ.symm j))).val
      (τ (σ.val (τ.symm k))).val
  exact ((isUnorderedRelabelling_symm A B τ hIso) i j k).trans
    ((σ.property (τ.symm i) (τ.symm j) (τ.symm k)).trans
      (hIso (σ.val (τ.symm i)) (σ.val (τ.symm j))
        (σ.val (τ.symm k))))

/-- Full finite automorphism groups of isomorphic unordered
presentations are explicitly equivalent by conjugation. -/
noncomputable def finiteHypergraphAutEquivOfRelabelling
    {a : Nat} (A B : EnumNode a)
    (τ : Equiv.Perm (Fin a))
    (hIso : IsUnorderedRelabelling A B τ) :
    FiniteHypergraphAut A.toOrdered3Graph a ≃
      FiniteHypergraphAut B.toOrdered3Graph a where
  toFun := relabelFiniteHypergraphAut A B τ hIso
  invFun :=
    relabelFiniteHypergraphAut B A τ.symm
      (isUnorderedRelabelling_symm A B τ hIso)
  left_inv := by
    intro σ
    apply Subtype.ext
    apply Equiv.ext
    intro i
    change τ.symm (τ (σ.val (τ.symm (τ i)))) = σ.val i
    simp
  right_inv := by
    intro σ
    apply Subtype.ext
    apply Equiv.ext
    intro i
    change τ (τ.symm (σ.val (τ (τ.symm i)))) = σ.val i
    simp

/-- The automorphism multiplier in the labelled big Ramsey degree
is independent of the arbitrary initial enumeration of A. -/
theorem finiteHypergraphAut_card_eq_of_relabelling
    {a : Nat} (A B : EnumNode a)
    (τ : Equiv.Perm (Fin a))
    (hIso : IsUnorderedRelabelling A B τ) :
    Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) =
      Fintype.card (FiniteHypergraphAut B.toOrdered3Graph a) := by
  classical
  exact Fintype.card_congr
    (finiteHypergraphAutEquivOfRelabelling A B τ hIso)

/-- The exact labelled degree formula, summing ALL increasing ordered
diary presentations and multiplying once by the automorphism group
size, is invariant under ANY unordered finite isomorphism.

This is a literal equality of natural numbers, independent of the
initial labels of the finite source A. -/
theorem exactOrderedDiaryDegree_eq_of_relabelling
    {a : Nat} (A B : EnumNode a)
    (τ : Equiv.Perm (Fin a))
    (hIso : IsUnorderedRelabelling A B τ) :
    (∑ P ∈ allIncreasingPresentations A,
      (unmarkedDiariesOfIncreasingPresentation A P).card) *
        Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) =
    (∑ P ∈ allIncreasingPresentations B,
      (unmarkedDiariesOfIncreasingPresentation B P).card) *
        Fintype.card (FiniteHypergraphAut B.toOrdered3Graph a) := by
  rw [← unmarkedDiaryCount_eq_sum_allIncreasingPresentations A,
      ← unmarkedDiaryCount_eq_sum_allIncreasingPresentations B,
      genuineUnmarkedDiaryCount_eq_of_relabelling A B τ hIso,
      finiteHypergraphAut_card_eq_of_relabelling A B τ hIso]

end ATRFiniteDecoder
end ThreeUniformDiaries
