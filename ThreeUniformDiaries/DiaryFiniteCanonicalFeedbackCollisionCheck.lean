import ThreeUniformDiaries.DiaryFiniteCanonicalFeedbackReduction
import ThreeUniformDiaries.DiaryFiniteTargetFlipCodeCheck

/-!
# Finite collision test for canonical geometric source-flip feedback

Canonical source codes have no duplicate representations. Thus
injectivity of the repaired feedback can be checked by a literal
pairwise separation of its geometric source pullback edge tables.

Moreover every genuine finite target flip is represented exactly
by one of finitely many full Boolean target edge tables, so checking
feedback injectivity for ALL target flips is equivalent to a FINITE
test on the actual target flip-code orbit and the actual canonical
source flip-code orbit.

This is a sound finite certificate for any proposed coherent
family of protected copies. It does NOT assert that such a family
passes the test for a general diary. No independent flip-control
coordinates or random Boolean cube are introduced.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For a fixed genuine target flip, canonical feedback is
injective iff distinct canonical source flips have different
literal source-size Boolean edge tables when pulled back through
their respectively selected bounded protected copies. -/
theorem canonical_feedback_injective_iff_pullback_codes_separate
    (A B T : Ordered3Graph Nat) (n k : Nat)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (FT : FiniteDiaryFlip B T k) :
    Function.Injective
      (realizedCanonicalSourceFlipFeedback
        A B T n k hCopies FT) ↔
      ∀ c d : {code : FiniteDiaryEdgeCode n //
          code ∈ finiteCanonicalSourceFlipCodes A n},
        finiteDiaryEdgeCode
          (finiteDiaryPullbackGraph T n
            (chosenCanonicalSourceFlipMap A B n k hCopies c)) n =
        finiteDiaryEdgeCode
          (finiteDiaryPullbackGraph T n
            (chosenCanonicalSourceFlipMap A B n k hCopies d)) n →
        c.val = d.val := by
  constructor
  · intro hInjective c d hCode
    have hFeedback :
        realizedCanonicalSourceFlipFeedback
          A B T n k hCopies FT c =
        realizedCanonicalSourceFlipFeedback
          A B T n k hCopies FT d := by
      apply Subtype.ext
      calc
        (realizedCanonicalSourceFlipFeedback
          A B T n k hCopies FT c).val =
            finiteDiaryEdgeCode
              (finiteDiaryPullbackGraph T n
                (chosenCanonicalSourceFlipMap
                  A B n k hCopies c)) n :=
          realizedCanonicalSourceFlipFeedback_val
            A B T n k hCopies FT c
        _ = finiteDiaryEdgeCode
              (finiteDiaryPullbackGraph T n
                (chosenCanonicalSourceFlipMap
                  A B n k hCopies d)) n := hCode
        _ = (realizedCanonicalSourceFlipFeedback
              A B T n k hCopies FT d).val :=
          (realizedCanonicalSourceFlipFeedback_val
            A B T n k hCopies FT d).symm
    exact congrArg Subtype.val (hInjective hFeedback)
  · intro hSeparate c d hEqual
    apply Subtype.ext
    apply hSeparate c d
    calc
      finiteDiaryEdgeCode
        (finiteDiaryPullbackGraph T n
          (chosenCanonicalSourceFlipMap A B n k hCopies c)) n =
        (realizedCanonicalSourceFlipFeedback
          A B T n k hCopies FT c).val :=
        (realizedCanonicalSourceFlipFeedback_val
          A B T n k hCopies FT c).symm
      _ = (realizedCanonicalSourceFlipFeedback
            A B T n k hCopies FT d).val :=
        congrArg Subtype.val hEqual
      _ = finiteDiaryEdgeCode
        (finiteDiaryPullbackGraph T n
          (chosenCanonicalSourceFlipMap A B n k hCopies d)) n :=
        realizedCanonicalSourceFlipFeedback_val
          A B T n k hCopies FT d

/-- Checking injectivity for ALL finite target flips is precisely
the following finite code-table test: test only TRUE target flip
codes and TRUE canonical source flip codes. -/
theorem canonical_feedback_all_flips_injective_iff_finite_codes
    (A B : Ordered3Graph Nat) (n k : Nat)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f) :
    (∀ T : Ordered3Graph Nat,
      ∀ FT : FiniteDiaryFlip B T k,
        Function.Injective
          (realizedCanonicalSourceFlipFeedback
            A B T n k hCopies FT)) ↔
    (∀ tcode : FiniteDiaryEdgeCode k,
      tcode ∈ finiteSourceFlipCodes B k →
      ∀ c d : {code : FiniteDiaryEdgeCode n //
          code ∈ finiteCanonicalSourceFlipCodes A n},
        finiteDiaryEdgeCode
          (finiteDiaryPullbackGraph
            (finiteDiaryCodeGraph k tcode) n
            (chosenCanonicalSourceFlipMap
              A B n k hCopies c)) n =
        finiteDiaryEdgeCode
          (finiteDiaryPullbackGraph
            (finiteDiaryCodeGraph k tcode) n
            (chosenCanonicalSourceFlipMap
              A B n k hCopies d)) n →
        c.val = d.val) := by
  constructor
  · intro hAll tcode hCode
    have FT : FiniteDiaryFlip B
        (finiteDiaryCodeGraph k tcode) k :=
      (mem_finiteSourceFlipCodes_iff B k tcode).mp hCode
    exact (canonical_feedback_injective_iff_pullback_codes_separate
      A B (finiteDiaryCodeGraph k tcode)
      n k hCopies FT).mp (hAll _ FT)
  · intro hCodes T FT
    let tcode := finiteDiaryEdgeCode T k
    have hRecon :
        finiteDiaryCodeGraph k tcode = T :=
      finiteDiaryCodeGraph_reconstruct T k
        FT.target_diary.prediary.frame
    have hCode : tcode ∈ finiteSourceFlipCodes B k :=
      (mem_finiteSourceFlipCodes_iff B k tcode).mpr (by
        rw [hRecon]
        exact FT)
    have hSeparate : ∀ c d : {code : FiniteDiaryEdgeCode n //
          code ∈ finiteCanonicalSourceFlipCodes A n},
        finiteDiaryEdgeCode
          (finiteDiaryPullbackGraph T n
            (chosenCanonicalSourceFlipMap A B n k hCopies c)) n =
        finiteDiaryEdgeCode
          (finiteDiaryPullbackGraph T n
            (chosenCanonicalSourceFlipMap A B n k hCopies d)) n →
        c.val = d.val := by
      simpa only [hRecon] using hCodes tcode hCode
    exact (canonical_feedback_injective_iff_pullback_codes_separate
      A B T n k hCopies FT).mpr hSeparate

/-- The strong every-target-flip absorption theorem follows from
an explicit finite separation certificate on source and target
FLIP ORBITS, instead of the impossible raw-code injectivity
premise. The existence of such certificates remains open. -/
theorem absorbsEveryTargetFlipInside_of_canonical_code_separation
    (A B : Ordered3Graph Nat) (n k : Nat)
    (DA : FiniteRoleDiaryBlock A n)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (hSeparate : ∀ tcode : FiniteDiaryEdgeCode k,
      tcode ∈ finiteSourceFlipCodes B k →
      ∀ c d : {code : FiniteDiaryEdgeCode n //
          code ∈ finiteCanonicalSourceFlipCodes A n},
        finiteDiaryEdgeCode
          (finiteDiaryPullbackGraph
            (finiteDiaryCodeGraph k tcode) n
            (chosenCanonicalSourceFlipMap
              A B n k hCopies c)) n =
        finiteDiaryEdgeCode
          (finiteDiaryPullbackGraph
            (finiteDiaryCodeGraph k tcode) n
            (chosenCanonicalSourceFlipMap
              A B n k hCopies d)) n →
        c.val = d.val) :
    AbsorbsEveryTargetFlipInside A B n k := by
  apply absorbsEveryTargetFlipInside_of_canonical_feedback_injective
    A B n k DA hCopies
  exact (canonical_feedback_all_flips_injective_iff_finite_codes
    A B n k hCopies).mpr hSeparate

end DiaryLeafPriority
end ThreeUniformDiaries
