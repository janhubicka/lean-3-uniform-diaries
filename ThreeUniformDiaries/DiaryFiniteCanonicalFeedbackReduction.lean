import ThreeUniformDiaries.DiaryFiniteCanonicalRealizedFeedback
import ThreeUniformDiaries.DiaryFiniteBoundedUniversality

/-!
# Corrected finite canonical-feedback reduction for target-flip absorption

The earlier geometric feedback reduction used ALL raw Boolean edge
tables on (Fin n)^3, including duplicate encodings of the same
diary. That feedback is never injective even under the identity
target flip, so its injectivity premise cannot be fulfilled.

The repaired feedback acts on canonical source-flip codes with a
genuine one-to-one correspondence to finite flip graphs. It is
always a closed self-map of the actual finite flip orbit and is
the identity under the identity target flip.

If for a suitably chosen finite target and fixed protected copy
family, the new CANONICAL feedback is injective for every genuine
target flip, finiteness yields a preimage of the original source
code. The verified exact pullback graph theorem upgrades that
preimage to a bounded mixed-meet-preserving source embedding.

The conditional hypothesis is now CONSISTENT with the identity
case. Its validity for arbitrary nontrivial target flips remains
the open geometric causality/injectivity problem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Correct finite-orbit feedback absorption: injectivity of the
CANONICAL self-map for every target flip gives strong bounded
unflipped-source embedding in every target flip. -/
theorem absorbsEveryTargetFlipInside_of_canonical_feedback_injective
    (A B : Ordered3Graph Nat) (n k : Nat)
    (DA : FiniteRoleDiaryBlock A n)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (hInjective : ∀ B' : Ordered3Graph Nat,
      ∀ F : FiniteDiaryFlip B B' k,
        Function.Injective
          (realizedCanonicalSourceFlipFeedback
            A B B' n k hCopies F)) :
    AbsorbsEveryTargetFlipInside A B n k := by
  classical
  intro B' F
  let feedback :=
    realizedCanonicalSourceFlipFeedback A B B' n k hCopies F
  let baseline : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n} :=
    ⟨finiteDiaryEdgeCode A n,
      finiteCanonicalSourceFlipCodes_baseline_mem DA⟩
  have hSurj : Function.Surjective feedback :=
    (Finite.injective_iff_surjective).mp (hInjective B' F)
  obtain ⟨c,hc⟩ := hSurj baseline
  let P := finiteDiaryCodeGraph n c.val
  let f := chosenCanonicalSourceFlipMap A B n k hCopies c
  have hRaw : c.val ∈ finiteSourceFlipCodes A n :=
    ((mem_finiteCanonicalSourceFlipCodes_iff A n c.val).mp
      c.property).1
  have FP : FiniteDiaryFlip A P n :=
    (mem_finiteSourceFlipCodes_iff A n c.val).mp hRaw
  have EP : FiniteBoundedMeetEmbedding P B n k f :=
    chosenCanonicalSourceFlipMap_spec A B n k hCopies c
  let Q := finiteDiaryPullbackGraph B' n f
  have FQ : FiniteDiaryFlip P Q n :=
    finiteDiaryPullbackGraph_is_sourceFlip
      FP.target_diary EP.toMeetEmbedding EP.image_bound F
  have hCode : finiteDiaryEdgeCode Q n =
      finiteDiaryEdgeCode A n := by
    have hVal := congrArg Subtype.val hc
    calc
      finiteDiaryEdgeCode Q n = (feedback c).val :=
        (realizedCanonicalSourceFlipFeedback_val
          A B B' n k hCopies F c).symm
      _ = baseline.val := hVal
      _ = finiteDiaryEdgeCode A n := rfl
  have hReconQ :
      finiteDiaryCodeGraph n (finiteDiaryEdgeCode Q n) = Q :=
    finiteDiaryCodeGraph_reconstruct Q n
      FQ.target_diary.prediary.frame
  have hReconA :
      finiteDiaryCodeGraph n (finiteDiaryEdgeCode A n) = A :=
    finiteDiaryCodeGraph_reconstruct A n DA.prediary.frame
  have hGraph : Q = A := by
    calc
      Q = finiteDiaryCodeGraph n (finiteDiaryEdgeCode Q n) :=
        hReconQ.symm
      _ = finiteDiaryCodeGraph n (finiteDiaryEdgeCode A n) :=
        congrArg (finiteDiaryCodeGraph n) hCode
      _ = A := hReconA
  have ETarget : FiniteBoundedMeetEmbedding Q B' n k f :=
    finiteDiaryPullbackGraph_boundedEmbedding_into_targetFlip
      FP.target_diary EP F
  refine ⟨f,?_⟩
  simpa only [hGraph] using ETarget

/-- Bounded finite universality produces a real finite target
containing one protected copy of every canonical source flip.
The geometric injectivity hypothesis for this fixed copy
family is the SINGLE remaining condition in the corrected
feedback approach to strong target-flip absorption. -/
theorem exists_finite_universal_target_canonical_feedback_reduction
    (A : Ordered3Graph Nat) (n : Nat)
    (DA : FiniteRoleDiaryBlock A n) :
    ∃ (B : Ordered3Graph Nat) (k : Nat),
      FiniteRoleDiaryBlock B k ∧
      ∃ hCopies :
        (∀ code : FiniteDiaryEdgeCode n,
          code ∈ finiteCanonicalSourceFlipCodes A n →
          ∃ f : Nat → Nat,
            FiniteBoundedMeetEmbedding
              (finiteDiaryCodeGraph n code) B n k f),
        (∀ B' : Ordered3Graph Nat,
          ∀ F : FiniteDiaryFlip B B' k,
            Function.Injective
              (realizedCanonicalSourceFlipFeedback
                A B B' n k hCopies F)) →
          AbsorbsEveryTargetFlipInside A B n k := by
  obtain ⟨B,k,DB,hUniversal⟩ :=
    exists_finiteDiary_for_all_source_flips_bounded A n DA
  have hCopies :
      ∀ code : FiniteDiaryEdgeCode n,
        code ∈ finiteCanonicalSourceFlipCodes A n →
        ∃ f : Nat → Nat,
          FiniteBoundedMeetEmbedding
            (finiteDiaryCodeGraph n code) B n k f := by
    intro code hc
    have hRaw : code ∈ finiteSourceFlipCodes A n :=
      ((mem_finiteCanonicalSourceFlipCodes_iff A n code).mp hc).1
    have hFlip : FiniteDiaryFlip A
        (finiteDiaryCodeGraph n code) n :=
      (mem_finiteSourceFlipCodes_iff A n code).mp hRaw
    exact hUniversal (finiteDiaryCodeGraph n code) hFlip
  refine ⟨B,k,DB,hCopies,?_⟩
  intro hInjective
  exact absorbsEveryTargetFlipInside_of_canonical_feedback_injective
    A B n k DA hCopies hInjective

end DiaryLeafPriority
end ThreeUniformDiaries
