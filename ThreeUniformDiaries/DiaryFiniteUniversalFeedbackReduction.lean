import ThreeUniformDiaries.DiaryFiniteRealizedFlipFeedback
import ThreeUniformDiaries.DiaryFiniteBoundedUniversality

/-!
# From verified finite universality to the remaining feedback task

The verified finite-family construction already produces a genuine
finite diary B containing bounded fully protected copies of EVERY
finite diary on a fixed source interval, hence certainly of every
genuine flip of A. The actual realisable source-flip orbit is a
finite set of literal ternary Boolean edge tables.

Therefore the source-flip feedback self-map developed in
DiaryFiniteRealizedFlipFeedback can ALWAYS be defined for SOME
finite universal target B with no additional existence axioms.

For that explicit (nonconstructively selected) target B and copy
family, the feedback map is automatically CLOSED on the finite
realisable source orbit. The strong every-target-flip absorption
statement follows if feedback INJECTIVITY holds under EVERY
target flip. This is a precise conditional reduction of the
entire remaining combinatorial task to its geometric injectivity
lemma; it does not claim to have established that lemma.

In particular, we do not assume a free Boolean cube of split
controls, and do not confuse a pulled-back source flip P with
the prescribed unflipped source A.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The verified bounded universality theorem supplies a single
finite target containing all genuine realisable source flips.
The remaining condition for this target is precisely that its
CANONICAL SOURCE-FLIP FEEDBACK is injective for each target flip,
in which case full range-correct absorption follows. -/
theorem exists_finite_universal_target_feedback_reduction
    (A : Ordered3Graph Nat) (n : Nat)
    (DA : FiniteRoleDiaryBlock A n) :
    ∃ (B : Ordered3Graph Nat) (k : Nat),
      FiniteRoleDiaryBlock B k ∧
      ∃ hCopies :
        (∀ code : FiniteDiaryEdgeCode n,
          code ∈ finiteSourceFlipCodes A n →
          ∃ f : Nat → Nat,
            FiniteBoundedMeetEmbedding
              (finiteDiaryCodeGraph n code) B n k f),
        (∀ B' : Ordered3Graph Nat,
          ∀ F : FiniteDiaryFlip B B' k,
            Function.Injective
              (realizedSourceFlipFeedback A B B' n k hCopies F)) →
          AbsorbsEveryTargetFlipInside A B n k := by
  obtain ⟨B,k,DB,hUniversal⟩ :=
    exists_finiteDiary_for_all_source_flips_bounded A n DA
  have hCopies :
      ∀ code : FiniteDiaryEdgeCode n,
        code ∈ finiteSourceFlipCodes A n →
        ∃ f : Nat → Nat,
          FiniteBoundedMeetEmbedding
            (finiteDiaryCodeGraph n code) B n k f := by
    intro code hCode
    have hFlip : FiniteDiaryFlip A (finiteDiaryCodeGraph n code) n :=
      (mem_finiteSourceFlipCodes_iff A n code).mp hCode
    exact hUniversal (finiteDiaryCodeGraph n code) hFlip
  refine ⟨B,k,DB,hCopies,?_⟩
  intro hInj
  exact absorbsEveryTargetFlipInside_of_feedback_injective
    A B n k DA hCopies hInj

end DiaryLeafPriority
end ThreeUniformDiaries
