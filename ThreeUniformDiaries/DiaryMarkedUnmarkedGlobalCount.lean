import ThreeUniformDiaries.DiaryUpperBoundUniformGenuineMarkedBound
import ThreeUniformDiaries.DiaryGenuineMarkingFibreCardinality

/-!
# Track C: exact global marked/unmarked diary source count

The genuine marked-diary list is already finite, complete, and
deduplicated (#1007). For a fixed genuine *unmarked* finite source
B, its complete A-leaf markings form a type equivalent to Aut(A)
(#1015). This file performs the remaining FINITE SUMMATION.

No large ambient diary, Ramsey statement, or unavoidability is
assumed. In particular this is a count of genuine FINITE source
diagrams with marked leaf tuples, and not a claim that the
manuscript's phrase "diaries of unordered A" already specifies
the same collection of all increasing presentations.

The proof groups marked sources by their underlying full diary
source, identifies each fibre with its genuine marking subtype,
and applies the checked automorphism-fibre equivalence. There is
no second automorphism factor hidden in the palette length.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- The deduplicated finite set of every actual marked full diary
whose complete genuine leaves induce the given unordered A. -/
noncomputable def allGenuineMarkedDiaryFinset
    {a : Nat} (A : EnumNode a) :
    Finset (MarkedFiniteSource 0 a) := by
  classical
  exact (allGenuineMarkedDiaryShapes A).toFinset

/-- Forget the marking, and deduplicate the resulting full finite
diary source diagrams. These are enumerated source shapes, not
different labelings of their same leaf reduct. -/
noncomputable def allGenuineUnmarkedDiarySources
    {a : Nat} (A : EnumNode a) :
    Finset (ProtectedSource 0) := by
  classical
  exact (allGenuineMarkedDiaryFinset A).image
    (fun T => T.source)

/-- Exact finite membership, with no extra size cutoff. -/
theorem mem_allGenuineMarkedDiaryFinset_iff
    {a : Nat} (A : EnumNode a)
    (T : MarkedFiniteSource 0 a) :
    T ∈ allGenuineMarkedDiaryFinset A ↔
      IsGenuineMarkedDiaryShape A T := by
  classical
  simpa [allGenuineMarkedDiaryFinset] using
    (mem_allGenuineMarkedDiaryShapes_iff A T)

/-- A source belongs to the unmarked family iff it has at least
one actual complete-leaf A-marking. In particular every source
in this family has a nonempty Aut(A) marking torsor. -/
theorem mem_allGenuineUnmarkedDiarySources_iff
    {a : Nat} (A : EnumNode a)
    (S : ProtectedSource 0) :
    S ∈ allGenuineUnmarkedDiarySources A ↔
      Nonempty (GenuineDiaryMarkingFibre A S) := by
  classical
  constructor
  · intro h
    obtain ⟨T, hT, hEq⟩ := Finset.mem_image.mp h
    have hShape : IsGenuineMarkedDiaryShape A T :=
      (mem_allGenuineMarkedDiaryFinset_iff A T).mp hT
    cases hEq
    exact ⟨⟨T.marked, hShape⟩⟩
  · rintro ⟨p⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨S,p.val⟩, ?_, rfl⟩
    exact (mem_allGenuineMarkedDiaryFinset_iff A
      ⟨S,p.val⟩).mpr p.property

/-- A literal equivalence between the deduplicated finite
marked-source list and the disjoint union of actual marking
fibres over the distinct unmarked full finite diary sources. -/
noncomputable def allGenuineMarked_unmarkedSigmaEquiv
    {a : Nat} (A : EnumNode a) :
    (↑(allGenuineMarkedDiaryFinset A)) ≃
      (Σ S : ↑(allGenuineUnmarkedDiarySources A),
        GenuineDiaryMarkingFibre A S.val) := by
  classical
  refine {
    toFun := fun T =>
      ⟨⟨T.val.source, Finset.mem_image.mpr
        ⟨T.val, T.property, rfl⟩⟩,
        ⟨T.val.marked,
          (mem_allGenuineMarkedDiaryFinset_iff A T.val).mp
            T.property⟩⟩
    invFun := fun Q =>
      ⟨⟨Q.1.val, Q.2.val⟩,
        (mem_allGenuineMarkedDiaryFinset_iff A
          ⟨Q.1.val, Q.2.val⟩).mpr Q.2.property⟩
    left_inv := ?_
    right_inv := ?_
  }
  · rintro ⟨T, hT⟩
    apply Subtype.ext
    cases T
    rfl
  · rintro ⟨⟨S, hS⟩, ⟨p, hp⟩⟩
    rfl

/-- Every source in the unmarked family supplies a concrete
basepoint, hence an actual finite instance for its marking fibre.
No choice of an *ordered presentation* of A is required here. -/
noncomputable def unmarkedGenuineSource_markingFintype
    {a : Nat} (A : EnumNode a)
    (S : ↑(allGenuineUnmarkedDiarySources A)) :
    Fintype (GenuineDiaryMarkingFibre A S.val) :=
  genuineDiaryMarkingFibre_fintype A S.val
    (Classical.choice
      ((mem_allGenuineUnmarkedDiarySources_iff A S.val).mp
        S.property))

/-- Actual cardinal multiplication, with the factor Aut(A) included
EXACTLY ONCE. This counts all possible genuine marked diary types
by first forgetting the marking, and then summing the constant-size
Aut(A) fibres of the forgetful map. -/
theorem allGenuineMarkedFinset_card_eq_unmarked_mul_aut
    {a : Nat} (A : EnumNode a) :
    (allGenuineMarkedDiaryFinset A).card =
      (allGenuineUnmarkedDiarySources A).card *
        Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) := by
  classical
  let M := allGenuineMarkedDiaryFinset A
  let U := allGenuineUnmarkedDiarySources A
  letI : ∀ S : ↑U, Fintype (GenuineDiaryMarkingFibre A S.val) :=
    fun S => unmarkedGenuineSource_markingFintype A S
  calc
    M.card = Fintype.card (↑M) := by simp
    _ = Fintype.card
        (Σ S : ↑U, GenuineDiaryMarkingFibre A S.val) :=
      Fintype.card_congr (allGenuineMarked_unmarkedSigmaEquiv A)
    _ = ∑ S : ↑U, Fintype.card
        (GenuineDiaryMarkingFibre A S.val) := by
      simp only [Fintype.card_sigma]
    _ = ∑ _S : ↑U,
        Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) := by
      apply Finset.sum_congr rfl
      intro S _
      exact genuineDiaryMarkingFibre_card_eq_aut A S.val
        (Classical.choice
          ((mem_allGenuineUnmarkedDiarySources_iff A S.val).mp
            S.property))
    _ = U.card *
        Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) := by
      simp

/-- Exact length of the original deduplicated list, not merely the
cardinality of its auxiliary Finset representation. -/
theorem allGenuineMarkedDiaryFinset_card_eq_length
    {a : Nat} (A : EnumNode a) :
    (allGenuineMarkedDiaryFinset A).card =
      allGenuineMarkedDiaryCount A := by
  classical
  simp [allGenuineMarkedDiaryFinset, allGenuineMarkedDiaryCount,
    allGenuineMarkedDiaryShapes, genuineMarkedDiaryFamily]

/-- The exact finite diary-count formula for the ACTUAL source
families used in the marked ATR Ramsey palette. The separate
editorial task is to identify the unmarked source count with
the manuscript's number of diaries across all increasing
presentations of unordered A. -/
theorem allGenuineMarkedDiaryCount_eq_unmarked_mul_aut
    {a : Nat} (A : EnumNode a) :
    allGenuineMarkedDiaryCount A =
      (allGenuineUnmarkedDiarySources A).card *
        Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) := by
  rw [← allGenuineMarkedDiaryFinset_card_eq_length A]
  exact allGenuineMarkedFinset_card_eq_unmarked_mul_aut A

end ATRFiniteDecoder
end ThreeUniformDiaries
