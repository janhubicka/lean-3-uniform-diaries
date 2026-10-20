import ThreeUniformDiaries.DiaryFiniteCanonicalCodeHitting
import ThreeUniformDiaries.DiaryFiniteSourceFlipCodeOrbit

/-!
# The actual finite set of source flips seen inside each target flip

Fix a finite family X of genuine protected embeddings f : A -> B.
For every target flip T of B, pull back the FULL induced edge table
of T along each f in X and encode that source-size table by a
finite ternary Boolean word.

These are actual source flips, not arbitrary independently chosen
split-control words: the canonical geometric pullback theorem
proves every code belongs to the REALISABLE finite source flip
orbit. This is a concrete finite set-valued invariant of T.

A member of X still embeds the *unflipped* A into T precisely
when the observed set of source codes contains the baseline code.
This gives a bounded, fully mixed-meet-correct finite hitting
formulation of the unresolved every-target-flip absorption step.

No claim that the observed sets cover the baseline in all target
flips is made. Nor is any self-map or invariant-family permutation
assumed without a geometric construction.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The finite set of genuine source-size Boolean edge tables
observed by pulling a target diary T back along all prescribed
source-copy maps g in X. -/
noncomputable def finitePullbackCodesOnCopies
    (T : Ordered3Graph Nat) (n : Nat)
    (X : Finset (Nat → Nat)) : Finset (FiniteDiaryEdgeCode n) := by
  classical
  exact X.image
    (fun g => finiteDiaryEdgeCode (finiteDiaryPullbackGraph T n g) n)

/-- Membership in the set-valued geometric pullback is exactly
existence of one of the prescribed maps producing this code. -/
theorem mem_finitePullbackCodesOnCopies_iff
    (T : Ordered3Graph Nat) (n : Nat)
    (X : Finset (Nat → Nat)) (code : FiniteDiaryEdgeCode n) :
    code ∈ finitePullbackCodesOnCopies T n X ↔
      ∃ g : Nat → Nat, g ∈ X ∧
        finiteDiaryEdgeCode (finiteDiaryPullbackGraph T n g) n =
          code := by
  classical
  simp [finitePullbackCodesOnCopies]

variable {A B T : Ordered3Graph Nat} {n k : Nat}

/-- All codes actually seen in a target flip from a protected
source-copy family lie in the true finite source flip orbit.
No fake free-cube control word enters the construction. -/
theorem finitePullbackCodesOnCopies_subset_realized_flips
    (DA : FiniteRoleDiaryBlock A n)
    (X : Finset (Nat → Nat))
    (hCopies : ∀ g : Nat → Nat, g ∈ X →
      FiniteBoundedMeetEmbedding A B n k g)
    (FT : FiniteDiaryFlip B T k) :
    finitePullbackCodesOnCopies T n X ⊆
      finiteSourceFlipCodes A n := by
  intro code hCode
  obtain ⟨g,hg,hEq⟩ :=
    (mem_finitePullbackCodesOnCopies_iff T n X code).mp hCode
  rw [← hEq]
  exact finiteDiaryPullbackGraph_code_mem_sourceFlips
    DA (hCopies g hg) FT

/-- A prescribed family of source copies has an unflipped
bounded protected copy in a given target flip iff its observed
finite source-code set contains the literal baseline source code. -/
theorem finitePullbackCodesOnCopies_baseline_mem_iff
    (DA : FiniteRoleDiaryBlock A n)
    (X : Finset (Nat → Nat))
    (hCopies : ∀ g : Nat → Nat, g ∈ X →
      FiniteBoundedMeetEmbedding A B n k g)
    (FT : FiniteDiaryFlip B T k) :
    finiteDiaryEdgeCode A n ∈ finitePullbackCodesOnCopies T n X ↔
      ∃ g : Nat → Nat, g ∈ X ∧
        FiniteBoundedMeetEmbedding A T n k g := by
  constructor
  · intro h
    obtain ⟨g,hg,hCode⟩ :=
      (mem_finitePullbackCodesOnCopies_iff
        T n X (finiteDiaryEdgeCode A n)).mp h
    exact ⟨g,hg,
      (finiteDiaryPullbackGraph_code_eq_source_iff_embedding
        DA (hCopies g hg) FT).mp hCode⟩
  · rintro ⟨g,hg,hEmbedding⟩
    exact (mem_finitePullbackCodesOnCopies_iff
      T n X (finiteDiaryEdgeCode A n)).mpr
        ⟨g,hg,
          (finiteDiaryPullbackGraph_code_eq_source_iff_embedding
            DA (hCopies g hg) FT).mpr hEmbedding⟩

/-- For a nonempty finite family of genuine source copies of A
in B itself, the observed code set at the BASELINE target B
contains the baseline source code. This is a necessary starting
point, not a proof of persistence under arbitrary flips. -/
theorem finitePullbackCodesOnCopies_baseline_target_mem
    (DA : FiniteRoleDiaryBlock A n)
    (DB : FiniteRoleDiaryBlock B k)
    (X : Finset (Nat → Nat)) (hX : X.Nonempty)
    (hCopies : ∀ g : Nat → Nat, g ∈ X →
      FiniteBoundedMeetEmbedding A B n k g) :
    finiteDiaryEdgeCode A n ∈ finitePullbackCodesOnCopies B n X := by
  obtain ⟨g,hg⟩ := hX
  exact (finitePullbackCodesOnCopies_baseline_mem_iff
    DA X hCopies (FiniteDiaryFlip.refl DB)).mpr
      ⟨g,hg,hCopies g hg⟩

/-- CONCRETE SUFFICIENT HITTING CRITERION:
if the baseline finite source edge code is observed in every
target flip from one fixed family of protected copies in B,
then the strong range-correct every-target-flip absorption
statement follows. The required hitting hypothesis remains the
unsolved geometric/combinatorial task. -/
theorem absorbsEveryTargetFlipInside_of_observed_codes
    (DA : FiniteRoleDiaryBlock A n)
    (X : Finset (Nat → Nat))
    (hCopies : ∀ g : Nat → Nat, g ∈ X →
      FiniteBoundedMeetEmbedding A B n k g)
    (hHits : ∀ T : Ordered3Graph Nat, FiniteDiaryFlip B T k →
      finiteDiaryEdgeCode A n ∈ finitePullbackCodesOnCopies T n X) :
    AbsorbsEveryTargetFlipInside A B n k := by
  intro T FT
  exact (finitePullbackCodesOnCopies_baseline_mem_iff
    DA X hCopies FT).mp (hHits T FT)

end DiaryLeafPriority
end ThreeUniformDiaries
