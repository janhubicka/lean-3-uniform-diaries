import ThreeUniformDiaries.DiaryFiniteSourceFlipCodeOrbit
import ThreeUniformDiaries.DiaryFinitePullbackProtectedEmbedding
import ThreeUniformDiaries.DiaryFiniteUniversalEdgeCode

/-!
# A canonical feedback SELF-MAP of the true finite source-flip orbit

The verified finite-family universality theorem supplies a finite
target diary B containing a fully protected copy of EVERY genuine
finite flip of a source A. For any such B and any target flip B'
of B, choose one protected embedding of each genuine source flip
P into B, and pull B' back along that chosen map.

The canonical pullback is a genuine flip of P, hence by flip
transitivity it belongs to the SAME realisable flip orbit of A.
This proves orbit CLOSURE unconditionally. It does not treat
split controls as independent or identify invalid Boolean words
with genuine diary flips.

The feedback map on the finite subtype of REALISABLE source
edge codes is now well defined. If it is injective for every
target flip B', it is automatically surjective (finite set), so
the baseline code of A occurs as one canonical pullback. The
fully protected pullback embedding then gives the STRONG
every-target-flip absorption property with range bounds.

**Only the implication from feedback injectivity to absorption is
proved.** Injectivity of the actual geometric feedback is the
unresolved constrained causal task; it is not an axiom of a diary
or an assumption that the entire Boolean control cube is valid.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For every realised source flip code select one fixed bounded,
fully protected embedding into the chosen finite target B.
Only TRUE source flip codes have to be assigned embeddings. -/
noncomputable def chosenRealizedSourceFlipMap
    (A B : Ordered3Graph Nat) (n k : Nat)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteSourceFlipCodes A n}) : Nat → Nat := by
  classical
  exact Classical.choose (hCopies c.val c.property)

/-- The chosen map really is a bounded full finite diary meet
embedding of the represented genuine source flip. -/
theorem chosenRealizedSourceFlipMap_spec
    (A B : Ordered3Graph Nat) (n k : Nat)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteSourceFlipCodes A n}) :
    FiniteBoundedMeetEmbedding
      (finiteDiaryCodeGraph n c.val) B n k
      (chosenRealizedSourceFlipMap A B n k hCopies c) := by
  classical
  exact Classical.choose_spec (hCopies c.val c.property)

/-- The canonical geometric pullback induces an ACTUAL self-map
of the finite realised source-flip orbit: each source flip P has
a chosen embedded copy in B; pulling an arbitrary target flip B'
back along it gives another true flip of P, and therefore of A.
Closure under this operation is PROVED, not postulated. -/
noncomputable def realizedSourceFlipFeedback
    (A B B' : Ordered3Graph Nat) (n k : Nat)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (F : FiniteDiaryFlip B B' k) :
    {code : FiniteDiaryEdgeCode n //
      code ∈ finiteSourceFlipCodes A n} →
    {code : FiniteDiaryEdgeCode n //
      code ∈ finiteSourceFlipCodes A n} := by
  classical
  intro c
  let P := finiteDiaryCodeGraph n c.val
  let f := chosenRealizedSourceFlipMap A B n k hCopies c
  have FP : FiniteDiaryFlip A P n :=
    (mem_finiteSourceFlipCodes_iff A n c.val).mp c.property
  have EP : FiniteBoundedMeetEmbedding P B n k f :=
    chosenRealizedSourceFlipMap_spec A B n k hCopies c
  refine ⟨finiteDiaryEdgeCode
      (finiteDiaryPullbackGraph B' n f) n, ?_⟩
  change finiteDiaryEdgeCode (finiteDiaryPullbackGraph B' n f) n ∈
    finiteSourceFlipCodes A n
  rw [finiteSourceFlipCodes_eq_of_flip FP]
  exact finiteDiaryPullbackGraph_code_mem_sourceFlips
    FP.target_diary EP F

/-- The value of the feedback is precisely the Boolean code of
the FULL induced source pullback, rather than a guessed vector of
independent split controls. -/
theorem realizedSourceFlipFeedback_val
    (A B B' : Ordered3Graph Nat) (n k : Nat)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (F : FiniteDiaryFlip B B' k)
    (c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteSourceFlipCodes A n}) :
    (realizedSourceFlipFeedback A B B' n k hCopies F c).val =
      finiteDiaryEdgeCode
        (finiteDiaryPullbackGraph B' n
          (chosenRealizedSourceFlipMap A B n k hCopies c)) n := by
  rfl

/-- Conditional finite-orbit absorption:
Given protected copies of ALL realisable flips, if the actual
geometric feedback map on the FINITE realised orbit is injective
for every target flip, then a preimage of A's baseline code
exists and the corresponding chosen map embeds unflipped A into
that target flip with all mixed numerical meets and range bounds.

The missing geometric INJECTIVITY assumption is explicit and
must be independently proved for a suitable diary construction. -/
theorem absorbsEveryTargetFlipInside_of_feedback_injective
    (A B : Ordered3Graph Nat) (n k : Nat)
    (DA : FiniteRoleDiaryBlock A n)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (hInjective : ∀ B' : Ordered3Graph Nat,
      ∀ F : FiniteDiaryFlip B B' k,
        Function.Injective
          (realizedSourceFlipFeedback A B B' n k hCopies F)) :
    AbsorbsEveryTargetFlipInside A B n k := by
  classical
  intro B' F
  let e := realizedSourceFlipFeedback A B B' n k hCopies F
  let baseline : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteSourceFlipCodes A n} :=
    ⟨finiteDiaryEdgeCode A n,
      finiteSourceFlipCodes_baseline_mem DA⟩
  have heSurj : Function.Surjective e :=
    (Finite.injective_iff_surjective).mp (hInjective B' F)
  obtain ⟨c,hc⟩ := heSurj baseline
  let P := finiteDiaryCodeGraph n c.val
  let f := chosenRealizedSourceFlipMap A B n k hCopies c
  have FP : FiniteDiaryFlip A P n :=
    (mem_finiteSourceFlipCodes_iff A n c.val).mp c.property
  have EP : FiniteBoundedMeetEmbedding P B n k f :=
    chosenRealizedSourceFlipMap_spec A B n k hCopies c
  have hPullFlip : FiniteDiaryFlip P
      (finiteDiaryPullbackGraph B' n f) n :=
    finiteDiaryPullbackGraph_is_sourceFlip
      FP.target_diary EP.toMeetEmbedding EP.image_bound F
  have hCode :
      finiteDiaryEdgeCode (finiteDiaryPullbackGraph B' n f) n =
        finiteDiaryEdgeCode A n := by
    have hVal := congrArg Subtype.val hc
    simpa only [realizedSourceFlipFeedback_val,
      baseline, e, f] using hVal
  have hReconPull : finiteDiaryCodeGraph n
      (finiteDiaryEdgeCode (finiteDiaryPullbackGraph B' n f) n) =
        finiteDiaryPullbackGraph B' n f :=
    finiteDiaryCodeGraph_reconstruct
      (finiteDiaryPullbackGraph B' n f) n
      hPullFlip.target_diary.prediary.frame
  have hReconA : finiteDiaryCodeGraph n
      (finiteDiaryEdgeCode A n) = A :=
    finiteDiaryCodeGraph_reconstruct A n DA.prediary.frame
  have hGraph : finiteDiaryPullbackGraph B' n f = A := by
    calc
      finiteDiaryPullbackGraph B' n f =
          finiteDiaryCodeGraph n
            (finiteDiaryEdgeCode (finiteDiaryPullbackGraph B' n f) n) :=
              hReconPull.symm
      _ = finiteDiaryCodeGraph n (finiteDiaryEdgeCode A n) :=
        congrArg (finiteDiaryCodeGraph n) hCode
      _ = A := hReconA
  have EP' : FiniteBoundedMeetEmbedding
      (finiteDiaryPullbackGraph B' n f) B' n k f :=
    finiteDiaryPullbackGraph_boundedEmbedding_into_targetFlip
      FP.target_diary EP F
  refine ⟨f, ?_⟩
  simpa only [hGraph] using EP'

end DiaryLeafPriority
end ThreeUniformDiaries
