import ThreeUniformDiaries.DiaryFiniteCanonicalFeedbackReduction

/-!
# Canonical feedback with EXPLICIT fixed geometric source-copy maps

The older feedback takes an existence proof for one bounded source
flip copy per canonical code, and then uses Classical.choose to
select the map. This is harmless for an abstract conditional
reduction but WRONG for a causal geometric proof: the selected maps
need not coincide with the explicitly constructed sign-rooted maps
whose common-prefix intersection properties are known.

Here the fixed maps are part of the theorem's INPUT. Every pullback
and every separation test uses exactly maps c, not unspecified
witnesses. Closure on the true canonical source-flip orbit,
identity action for the trivial target flip and finite
injectivity→surjectivity→bounded target-flip absorption are
proved from the SAME actual bounded source-copy certificates.

This does not assert that the sign-rooted maps satisfy the
injectivity condition for all target flips; that is the next
geometric theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

noncomputable def explicitCanonicalSourceFlipFeedback
    (A B B' : Ordered3Graph Nat) (n k : Nat)
    (maps : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n} → Nat → Nat)
    (hMaps : ∀ c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n},
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n c.val) B n k (maps c))
    (F : FiniteDiaryFlip B B' k) :
    {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n} →
    {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n} := by
  classical
  intro c
  let P := finiteDiaryCodeGraph n c.val
  let f := maps c
  have hRaw : c.val ∈ finiteSourceFlipCodes A n :=
    ((mem_finiteCanonicalSourceFlipCodes_iff A n c.val).mp
      c.property).1
  have FP : FiniteDiaryFlip A P n :=
    (mem_finiteSourceFlipCodes_iff A n c.val).mp hRaw
  have EP : FiniteBoundedMeetEmbedding P B n k f :=
    hMaps c
  let Q := finiteDiaryPullbackGraph B' n f
  have FQ : FiniteDiaryFlip P Q n :=
    finiteDiaryPullbackGraph_is_sourceFlip
      FP.target_diary EP.toMeetEmbedding EP.image_bound F
  have FAQ : FiniteDiaryFlip A Q n := FP.trans FQ
  have hQRecon :
      finiteDiaryCodeGraph n (finiteDiaryEdgeCode Q n) = Q :=
    finiteDiaryCodeGraph_reconstruct Q n
      FQ.target_diary.prediary.frame
  have hQCode : finiteDiaryEdgeCode Q n ∈
      finiteCanonicalSourceFlipCodes A n := by
    apply (mem_finiteCanonicalSourceFlipCodes_iff A n _).mpr
    constructor
    · exact (mem_finiteSourceFlipCodes_iff A n _).mpr (by
        rw [hQRecon]
        exact FAQ)
    · unfold IsCanonicalFiniteDiaryEdgeCode
      rw [hQRecon]
  exact ⟨finiteDiaryEdgeCode Q n, hQCode⟩

/-- The value of corrected feedback is the actual Boolean table
of the literal source pullback along its selected bounded map. -/
theorem explicitCanonicalSourceFlipFeedback_val
    (A B B' : Ordered3Graph Nat) (n k : Nat)
    (maps : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n} → Nat → Nat)
    (hMaps : ∀ c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n},
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n c.val) B n k (maps c))
    (F : FiniteDiaryFlip B B' k)
    (c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n}) :
    (explicitCanonicalSourceFlipFeedback A B B' n k maps hMaps F c).val =
      finiteDiaryEdgeCode
        (finiteDiaryPullbackGraph B' n
          (maps c)) n := by
  rfl

/-- Under the IDENTITY target flip, corrected feedback fixes
EVERY canonical source flip code, independent of copy selection. -/
theorem explicitCanonicalSourceFlipFeedback_refl_eq
    (A B : Ordered3Graph Nat) (n k : Nat)
    (DB : FiniteRoleDiaryBlock B k)
    (maps : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n} → Nat → Nat)
    (hMaps : ∀ c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n},
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n c.val) B n k (maps c))
    (c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n}) :
    explicitCanonicalSourceFlipFeedback A B B n k maps hMaps
      (FiniteDiaryFlip.refl DB) c = c := by
  let P := finiteDiaryCodeGraph n c.val
  let f := maps c
  have hRaw : c.val ∈ finiteSourceFlipCodes A n :=
    ((mem_finiteCanonicalSourceFlipCodes_iff A n c.val).mp
      c.property).1
  have FP : FiniteDiaryFlip A P n :=
    (mem_finiteSourceFlipCodes_iff A n c.val).mp hRaw
  have EP : FiniteBoundedMeetEmbedding P B n k f :=
    hMaps c
  have hPull : finiteDiaryPullbackGraph B n f = P :=
    (finiteDiaryPullbackGraph_eq_source_iff_boundedEmbedding
      FP.target_diary EP (FiniteDiaryFlip.refl DB)).mpr EP
  have hCanonical :
      finiteDiaryEdgeCode P n = c.val :=
    ((mem_finiteCanonicalSourceFlipCodes_iff A n c.val).mp
      c.property).2
  apply Subtype.ext
  calc
    (explicitCanonicalSourceFlipFeedback A B B n k maps hMaps
        (FiniteDiaryFlip.refl DB) c).val =
        finiteDiaryEdgeCode (finiteDiaryPullbackGraph B n f) n :=
      explicitCanonicalSourceFlipFeedback_val
        A B B n k maps hMaps (FiniteDiaryFlip.refl DB) c
    _ = finiteDiaryEdgeCode P n := congrArg
      (fun X : Ordered3Graph Nat => finiteDiaryEdgeCode X n) hPull
    _ = c.val := hCanonical

/-- In particular, the repaired feedback IS INJECTIVE for the
unflipped target. This failed on the old noncanonical raw orbit. -/
theorem explicitCanonicalSourceFlipFeedback_refl_injective
    (A B : Ordered3Graph Nat) (n k : Nat)
    (DB : FiniteRoleDiaryBlock B k)
    (maps : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n} → Nat → Nat)
    (hMaps : ∀ c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n},
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n c.val) B n k (maps c)) :
    Function.Injective
      (explicitCanonicalSourceFlipFeedback A B B n k maps hMaps
        (FiniteDiaryFlip.refl DB)) := by
  intro c d h
  calc
    c = explicitCanonicalSourceFlipFeedback A B B n k maps hMaps
          (FiniteDiaryFlip.refl DB) c :=
        (explicitCanonicalSourceFlipFeedback_refl_eq
          A B n k DB maps hMaps c).symm
    _ = explicitCanonicalSourceFlipFeedback A B B n k maps hMaps
          (FiniteDiaryFlip.refl DB) d := h
    _ = d := explicitCanonicalSourceFlipFeedback_refl_eq
      A B n k DB maps hMaps d


/-- The permutation argument for an actual, EXPLICIT, coherent
family of bounded source maps. Geometric injectivity for every
target flip gives the strong bounded absorption property. The
hypothesis is not silently transferred to arbitrary
Classical.choose copies. -/
theorem absorbsEveryTargetFlipInside_of_explicit_feedback_injective
    (A B : Ordered3Graph Nat) (n k : Nat)
    (DA : FiniteRoleDiaryBlock A n)
    (maps : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n} → Nat → Nat)
    (hMaps : ∀ c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n},
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n c.val) B n k (maps c))
    (hInjective : ∀ B' : Ordered3Graph Nat,
      ∀ F : FiniteDiaryFlip B B' k,
        Function.Injective
          (explicitCanonicalSourceFlipFeedback
            A B B' n k maps hMaps F)) :
    AbsorbsEveryTargetFlipInside A B n k := by
  classical
  intro B' F
  let feedback :=
    explicitCanonicalSourceFlipFeedback A B B' n k maps hMaps F
  let baseline : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n} :=
    ⟨finiteDiaryEdgeCode A n,
      finiteCanonicalSourceFlipCodes_baseline_mem DA⟩
  have hSurj : Function.Surjective feedback :=
    (Finite.injective_iff_surjective).mp (hInjective B' F)
  obtain ⟨c,hc⟩ := hSurj baseline
  let P := finiteDiaryCodeGraph n c.val
  let f := maps c
  have hRaw : c.val ∈ finiteSourceFlipCodes A n :=
    ((mem_finiteCanonicalSourceFlipCodes_iff A n c.val).mp
      c.property).1
  have FP : FiniteDiaryFlip A P n :=
    (mem_finiteSourceFlipCodes_iff A n c.val).mp hRaw
  have EP : FiniteBoundedMeetEmbedding P B n k f :=
    hMaps c
  let Q := finiteDiaryPullbackGraph B' n f
  have FQ : FiniteDiaryFlip P Q n :=
    finiteDiaryPullbackGraph_is_sourceFlip
      FP.target_diary EP.toMeetEmbedding EP.image_bound F
  have hCode : finiteDiaryEdgeCode Q n =
      finiteDiaryEdgeCode A n := by
    have hVal := congrArg Subtype.val hc
    calc
      finiteDiaryEdgeCode Q n = (feedback c).val :=
        (explicitCanonicalSourceFlipFeedback_val
          A B B' n k maps hMaps F c).symm
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



end DiaryLeafPriority
end ThreeUniformDiaries
