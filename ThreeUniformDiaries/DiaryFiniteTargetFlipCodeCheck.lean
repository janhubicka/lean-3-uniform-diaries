import ThreeUniformDiaries.DiaryFinitePullbackCodeFamily

/-!
# A genuinely FINITE target-flip test for prescribed source-copy families

The flip orbit of any finite diary B is represented without
loss by the finite set of all full ternary Boolean edge codes
of genuine flips of B. Every target flip is reconstructed
exactly from its code, and conversely every code in that set
is a true bounded finite diary flip.

Therefore the remaining prescribed-family pullback hitting
condition over ALL target flips is logically equivalent to
a condition quantified only over this FINITE set of genuine
target-flip codes. The inner observed set of source flip
codes is also finite. This gives a concrete finite test for
any PROPOSED family of protected source-copy maps.

It is important not to misstate the result: we do NOT prove
that a family passing this test exists, and the general
absorption theorem is NOT proved here. We also do not
assume independent Boolean split controls or replace the
actual finite flip relation by a free cube.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A B : Ordered3Graph Nat} {n k : Nat}

/-- The baseline-source-code hitting statement over all genuine
flips of a bounded target B is equivalent to the SAME statement
quantified over the finite code orbit of B, with literal
reconstruction of each finite target graph from its edge table.
No embedding or causality assumption is needed for this equivalence. -/
theorem finite_target_flip_code_check_iff
    (X : Finset (Nat → Nat)) :
    (∀ T : Ordered3Graph Nat, FiniteDiaryFlip B T k →
      finiteDiaryEdgeCode A n ∈ finitePullbackCodesOnCopies T n X) ↔
    (∀ code : FiniteDiaryEdgeCode k,
      code ∈ finiteSourceFlipCodes B k →
      finiteDiaryEdgeCode A n ∈
        finitePullbackCodesOnCopies
          (finiteDiaryCodeGraph k code) n X) := by
  constructor
  · intro h code hc
    exact h (finiteDiaryCodeGraph k code)
      ((mem_finiteSourceFlipCodes_iff B k code).mp hc)
  · intro h T FT
    have hT : finiteDiaryCodeGraph k (finiteDiaryEdgeCode T k) = T :=
      finiteDiaryCodeGraph_reconstruct T k
        FT.target_diary.prediary.frame
    have hc : finiteDiaryEdgeCode T k ∈ finiteSourceFlipCodes B k := by
      apply (mem_finiteSourceFlipCodes_iff B k
        (finiteDiaryEdgeCode T k)).mpr
      rw [hT]
      exact FT
    simpa only [hT] using h (finiteDiaryEdgeCode T k) hc

/-- For a nonempty family of genuine source embeddings into the
unflipped target, the baseline edge code occurs among the observed
source codes for the baseline target code. The actual finite
target-check theorem quantifies over ALL codes in the flip orbit. -/
theorem finite_target_code_baseline_member
    (DA : FiniteRoleDiaryBlock A n)
    (DB : FiniteRoleDiaryBlock B k)
    (X : Finset (Nat → Nat))
    (hX : X.Nonempty)
    (hCopies : ∀ g : Nat → Nat, g ∈ X →
      FiniteBoundedMeetEmbedding A B n k g) :
    finiteDiaryEdgeCode A n ∈
      finitePullbackCodesOnCopies B n X :=
  finitePullbackCodesOnCopies_baseline_target_mem
    DA DB X hX hCopies

/-- Explicit sufficient FINITE-CODE certificate for the strong
range-correct second flip property. Every target code belongs
to a finite enumeration of true flips, and the required baseline
source code is looked up in a finite image of prescribed maps.
The existence of such a certificate remains OPEN. -/
theorem absorbsEveryTargetFlipInside_of_finite_target_code_check
    (DA : FiniteRoleDiaryBlock A n)
    (X : Finset (Nat → Nat))
    (hCopies : ∀ g : Nat → Nat, g ∈ X →
      FiniteBoundedMeetEmbedding A B n k g)
    (hCodeHits : ∀ code : FiniteDiaryEdgeCode k,
      code ∈ finiteSourceFlipCodes B k →
      finiteDiaryEdgeCode A n ∈
        finitePullbackCodesOnCopies
          (finiteDiaryCodeGraph k code) n X) :
    AbsorbsEveryTargetFlipInside A B n k := by
  apply absorbsEveryTargetFlipInside_of_observed_codes
    DA X hCopies
  exact (finite_target_flip_code_check_iff
    (A := A) (B := B) (n := n) (k := k) X).mpr hCodeHits

end DiaryLeafPriority
end ThreeUniformDiaries
