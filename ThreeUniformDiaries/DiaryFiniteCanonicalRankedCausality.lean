import ThreeUniformDiaries.DiaryFiniteCanonicalFeedbackReduction

/-!
# Strictly ranked geometric correction implies canonical feedback injectivity

The canonical feedback of a finite target flip is a genuine self-map
of the finite source-flip orbit. The remaining geometric problem is
to ensure that this self-map has no collisions for nonidentity flips.

We record a concrete, checkable CAUSAL SUFFICIENT CONDITION. Choose a
rank on the actual (not necessarily increasing) source triple-index
positions. The Boolean "correction bit" at one index is

  (feedback output at that index) XOR (input code at that index).

If this correction depends only on input coordinates of STRICTLY
SMALLER rank, then the feedback is injective by induction on rank.
The theorem works on ANY subset of the code cube, in particular the
canonical orbit of genuine flips, and requires no false independent
flip-coordinate assumption.

The condition is not claimed for any actual protected-copy family.
This file makes the remaining geometric causality obligation precise,
with no suggested choice of rank hidden in a theorem statement.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A triangular XOR correction is injective even if its domain
is only a restricted finite family of realisable edge codes, and
even when several triple indices have the same rank. The proof
does not assume those indices are genuine flip controls. -/
theorem finiteCode_feedback_injective_of_ranked_correction
    (n : Nat)
    (S : Finset (FiniteDiaryEdgeCode n))
    (rank : Fin n → Fin n → Fin n → Nat)
    (F : {c : FiniteDiaryEdgeCode n // c ∈ S} →
      {c : FiniteDiaryEdgeCode n // c ∈ S})
    (hCausal : ∀
      (c d : {code : FiniteDiaryEdgeCode n // code ∈ S})
      (i j z : Fin n),
      (∀ a b t : Fin n, rank a b t < rank i j z →
        c.val a b t = d.val a b t) →
      Bool.xor ((F c).val i j z) (c.val i j z) =
        Bool.xor ((F d).val i j z) (d.val i j z)) :
    Function.Injective F := by
  intro c d hEqual
  apply Subtype.ext
  funext i j z
  have hAll : ∀ m : Nat, ∀ i j z : Fin n,
      rank i j z = m → c.val i j z = d.val i j z := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro x y t hr
      have hLower : ∀ a b u : Fin n,
          rank a b u < rank x y t →
          c.val a b u = d.val a b u := by
        intro a b u hlt
        exact ih (rank a b u) (by omega) a b u rfl
      have hCorrection := hCausal c d x y t hLower
      have hOut : (F c).val x y t = (F d).val x y t := by
        exact congrFun (congrFun
          (congrFun (congrArg Subtype.val hEqual) x) y) t
      rw [← hOut] at hCorrection
      cases hc : c.val x y t <;>
        cases hd : d.val x y t <;>
        cases ho : (F c).val x y t <;>
        simp_all [Bool.xor]
  exact hAll (rank i j z) i j z rfl

/-- If the ACTUAL canonical feedback under a chosen target flip
has strictly ranked XOR corrections on its true source flip
orbit, then that concrete feedback is injective. -/
theorem realizedCanonicalFeedback_injective_of_ranked_causality
    (A B T : Ordered3Graph Nat) (n k : Nat)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (FT : FiniteDiaryFlip B T k)
    (rank : Fin n → Fin n → Fin n → Nat)
    (hCausal : ∀
      (c d : {code : FiniteDiaryEdgeCode n //
        code ∈ finiteCanonicalSourceFlipCodes A n})
      (i j z : Fin n),
      (∀ a b t : Fin n, rank a b t < rank i j z →
        c.val a b t = d.val a b t) →
      Bool.xor
        ((realizedCanonicalSourceFlipFeedback
          A B T n k hCopies FT c).val i j z)
        (c.val i j z) =
      Bool.xor
        ((realizedCanonicalSourceFlipFeedback
          A B T n k hCopies FT d).val i j z)
        (d.val i j z)) :
    Function.Injective
      (realizedCanonicalSourceFlipFeedback
        A B T n k hCopies FT) :=
  finiteCode_feedback_injective_of_ranked_correction
    n (finiteCanonicalSourceFlipCodes A n)
    rank
    (realizedCanonicalSourceFlipFeedback
      A B T n k hCopies FT) hCausal

/-- A SINGLE triple-ranking whose actual canonical correction is
strictly prefix-causal for ALL genuine target flips suffices for
strong bounded every-target-flip absorption. This is deliberately
a conditional geometric criterion, not a proof of causality. -/
theorem absorbsEveryTargetFlipInside_of_ranked_causal_feedback
    (A B : Ordered3Graph Nat) (n k : Nat)
    (DA : FiniteRoleDiaryBlock A n)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (rank : Fin n → Fin n → Fin n → Nat)
    (hCausal : ∀ (T : Ordered3Graph Nat)
      (FT : FiniteDiaryFlip B T k)
      (c d : {code : FiniteDiaryEdgeCode n //
        code ∈ finiteCanonicalSourceFlipCodes A n})
      (i j z : Fin n),
      (∀ a b t : Fin n, rank a b t < rank i j z →
        c.val a b t = d.val a b t) →
      Bool.xor
        ((realizedCanonicalSourceFlipFeedback
          A B T n k hCopies FT c).val i j z)
        (c.val i j z) =
      Bool.xor
        ((realizedCanonicalSourceFlipFeedback
          A B T n k hCopies FT d).val i j z)
        (d.val i j z)) :
    AbsorbsEveryTargetFlipInside A B n k := by
  apply absorbsEveryTargetFlipInside_of_canonical_feedback_injective
    A B n k DA hCopies
  intro T FT
  exact realizedCanonicalFeedback_injective_of_ranked_causality
    A B T n k hCopies FT rank (hCausal T FT)

end DiaryLeafPriority
end ThreeUniformDiaries
