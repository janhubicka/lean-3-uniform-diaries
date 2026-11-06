import ThreeUniformDiaries.DiaryExactUnlabelledBigRamseyDegree
import ThreeUniformDiaries.DiaryExactDegreeRelabelInvariance
import ThreeUniformDiaries.DiaryUpperBoundLabelledCopyEquivalence

/-!
# Track A/C: unlabelled big Ramsey bounds do not depend on the labels of A

The exact unlabelled big Ramsey degree was checked in Track C #1124.
We prove a stronger elementary statement: for ANY ambient ordered graph
U, not necessarily countably universal, a relabelling of the finite
source A cannot change the unlabelled finite-colouring Ramsey bound.

The reason is literal equality of the allowed vertex-set copies.
An unordered isomorphism τ:A→B reindexes every actual labelled
B-copy as an actual labelled A-copy, preserving edges AND nonedges
and leaving the finite image SET unchanged. The same target
selfembedding and palette work in both directions.

This avoids invoking the numerical degree equality, genericity,
countable universality, or any countable diary unavoidability.
The separate checked full-diary source-family identity then proves
the canonical all-ordered-presentation unlabelled count is invariant.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- A truly induced labelled embedding remains one after
reindexing the finite source via an arbitrary unordered
isomorphism. The target vertex images need not be increasing. -/
theorem inducedLabelledCopy_of_unordered_relabelling
    {a : Nat} (A B : EnumNode a)
    (τ : Equiv.Perm (Fin a))
    (hIso : IsUnorderedRelabelling A B τ)
    (U : Ordered3Graph Nat)
    (v : Fin a → Nat)
    (hv : IsInducedLabelledCopy A U v) :
    IsInducedLabelledCopy B U (fun i => v (τ.symm i)) := by
  have hvFull :
      IsFiniteLabelledCopy A.toOrdered3Graph U a v :=
    (isInducedLabelledCopy_iff_fullUnordered A U v).mp hv
  apply (isInducedLabelledCopy_iff_fullUnordered
    B U (fun i => v (τ.symm i))).mpr
  refine ⟨hvFull.1.comp τ.symm.injective, ?_⟩
  intro i j k
  calc
    B.toOrdered3Graph.unorderedEdge i.val j.val k.val ↔
      A.toOrdered3Graph.unorderedEdge
        (τ.symm i).val (τ.symm j).val (τ.symm k).val :=
      isUnorderedRelabelling_symm A B τ hIso i j k
    _ ↔ U.unorderedEdge
        (v (τ.symm i)) (v (τ.symm j)) (v (τ.symm k)) :=
      hvFull.2 (τ.symm i) (τ.symm j) (τ.symm k)

/-- A finite image set does not depend on the order
of enumeration of its vertices, even with an arbitrary
nonmonotone target map g. -/
private theorem finiteImage_reindex_perm
    {a : Nat} (σ : Equiv.Perm (Fin a))
    (g : Fin a → Nat) :
    (Finset.univ : Finset (Fin a)).image (fun i => g (σ i)) =
      (Finset.univ : Finset (Fin a)).image g := by
  classical
  apply Finset.ext
  intro x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨σ i, hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨σ.symm i, ?_⟩
    simpa only [Equiv.apply_symm_apply] using hi

/-- The standard UNLABELLED finite-colouring big Ramsey bound
predicate is literally invariant under any isomorphism of
finite unordered sources. No universality assumption on U is
required: this is a direct transport of the colouring domain. -/
theorem unlabelledBigRamseyBound_iff_of_unordered_relabelling
    (U : Ordered3Graph Nat)
    {a : Nat} (A B : EnumNode a)
    (τ : Equiv.Perm (Fin a))
    (hIso : IsUnorderedRelabelling A B τ)
    (t : Nat) :
    IsUnlabelledBigRamseyBound U A t ↔
      IsUnlabelledBigRamseyBound U B t := by
  classical
  have transfer (X Y : EnumNode a) (σ : Equiv.Perm (Fin a))
      (hXY : IsUnorderedRelabelling X Y σ)
      (hBound : IsUnlabelledBigRamseyBound U X t) :
      IsUnlabelledBigRamseyBound U Y t := by
    intro κ _ _ χ
    obtain ⟨w, palette, hCard, hCover⟩ := hBound κ χ
    refine ⟨w, palette, hCard, ?_⟩
    intro v
    have hYX : IsUnorderedRelabelling Y X σ.symm :=
      isUnorderedRelabelling_symm X Y σ hXY
    let q : GenuineFiniteEmbeddings X U :=
      ⟨(fun i => v.val (σ i)), by
        simpa only [Equiv.symm_symm] using
          (inducedLabelledCopy_of_unordered_relabelling
            Y X σ.symm hYX U v.val v.property)⟩
    have hReindex :
        (Finset.univ : Finset (Fin a)).image
            (fun i => w (q.val i)) =
          (Finset.univ : Finset (Fin a)).image
            (fun i => w (v.val i)) := by
      change (Finset.univ : Finset (Fin a)).image
          (fun i => w (v.val (σ i))) =
        (Finset.univ : Finset (Fin a)).image
          (fun i => w (v.val i))
      exact finiteImage_reindex_perm σ (fun i => w (v.val i))
    have hp := hCover q
    change χ ((Finset.univ : Finset (Fin a)).image
      (fun i => w (q.val i))) ∈ palette at hp
    rw [hReindex] at hp
    exact hp
  constructor
  · exact transfer A B τ hIso
  · exact transfer B A τ.symm
      (isUnorderedRelabelling_symm A B τ hIso)

/-- In the canonical all-increasing-presentations counting
convention, the unlabelled diary count itself is invariant
under arbitrary finite unordered isomorphism. -/
theorem unlabelledOrderedDiarySum_eq_of_relabelling
    {a : Nat} (A B : EnumNode a)
    (τ : Equiv.Perm (Fin a))
    (hIso : IsUnorderedRelabelling A B τ) :
    (∑ P ∈ allIncreasingPresentations A,
        (unmarkedDiariesOfIncreasingPresentation A P).card) =
      (∑ P ∈ allIncreasingPresentations B,
        (unmarkedDiariesOfIncreasingPresentation B P).card) := by
  calc
    (∑ P ∈ allIncreasingPresentations A,
        (unmarkedDiariesOfIncreasingPresentation A P).card) =
      (allGenuineUnmarkedDiarySources A).card :=
        (unmarkedDiaryCount_eq_sum_allIncreasingPresentations A).symm
    _ = (allGenuineUnmarkedDiarySources B).card :=
      genuineUnmarkedDiaryCount_eq_of_relabelling A B τ hIso
    _ = (∑ P ∈ allIncreasingPresentations B,
        (unmarkedDiariesOfIncreasingPresentation B P).card) :=
      unmarkedDiaryCount_eq_sum_allIncreasingPresentations B

end ATRFiniteDecoder
end ThreeUniformDiaries
