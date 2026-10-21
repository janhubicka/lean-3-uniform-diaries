import ThreeUniformDiaries.DiaryFiniteCanonicalIncreasingSeparation
import ThreeUniformDiaries.DiaryFiniteCanonicalFeedbackReduction

/-!
# Prefix-causal corrections on genuine increasing hyperedges only

Canonical source flip codes are determined entirely by their
strictly increasing edge triples (verified #815). Any supposed
geometric causality proof should therefore speak ONLY about these
real incidences, not redundant Boolean-table positions.

Give source triples a natural-number rank. Assume that for each
genuine triple i<j<z the XOR correction bit

  feedback(c)[i,j,z] XOR c[i,j,z]

depends solely on source code bits at GENUINE triples of strictly
smaller rank. We do not require a free cube of independent flips,
a one-to-one rank, or any prefix condition on invalid triples.

Strong induction on rank proves feedback injectivity on the true
canonical source-flip orbit. This is the precise local causality
criterion needed for strong bounded every-target-flip absorption.

The geometric rank and its prefix-causality remain OPEN; this
module makes those assumptions explicit rather than claiming them.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Cancellation of an XOR correction sharing the same first bit.
Kept separate to prevent large dependent-context simplifications. -/
private theorem xor_cancel_left (p q r : Bool)
    (h : Bool.xor p q = Bool.xor p r) : q = r := by
  cases p <;> cases q <;> cases r <;> simp_all [Bool.xor]

/-- STRICTLY PREFIX-CAUSAL corrections on increasing source triples
give injectivity of the ACTUAL canonical geometric flip feedback.
Several triples are allowed the same rank; none may read corrections
of another triple at that rank. -/
theorem canonical_feedback_injective_of_ordered_ranked_causality
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
      i < j → j < z →
      (∀ a b t : Fin n,
        a < b → b < t → rank a b t < rank i j z →
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
        A B T n k hCopies FT) := by
  let feedback :=
    realizedCanonicalSourceFlipFeedback A B T n k hCopies FT
  intro c d hEqual
  apply Subtype.ext
  apply (canonical_source_codes_eq_iff_increasing_bits
    A n c.val d.val c.property d.property).mpr
  intro i j z hij hjz
  have hAll :
      ∀ m : Nat, ∀ x y t : Fin n,
        x < y → y < t → rank x y t = m →
        c.val x y t = d.val x y t := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro x y t hxy hyt hRank
      have hPrior : ∀ a b u : Fin n,
          a < b → b < u → rank a b u < rank x y t →
          c.val a b u = d.val a b u := by
        intro a b u hab hbu hLess
        exact ih (rank a b u) (by omega)
          a b u hab hbu rfl
      have hCorrection :=
        hCausal c d x y t hxy hyt hPrior
      have hOut : (feedback c).val x y t =
          (feedback d).val x y t := by
        exact congrFun (congrFun
          (congrFun (congrArg Subtype.val hEqual) x) y) t
      change Bool.xor ((feedback c).val x y t) (c.val x y t) =
        Bool.xor ((feedback d).val x y t) (d.val x y t)
        at hCorrection
      rw [← hOut] at hCorrection
      exact xor_cancel_left
        ((feedback c).val x y t) (c.val x y t) (d.val x y t)
        hCorrection
  exact hAll (rank i j z) i j z hij hjz rfl

/-- If one common rank makes the ACTUAL corrections strictly
prefix-causal on increasing source triples for ALL genuine
target flips, then the finite target absorbs every target flip
by a bounded, fully meet-preserving copy of the original source.
This is a conditional geometric reduction. -/
theorem absorbsEveryTargetFlipInside_of_ordered_ranked_causality
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
      i < j → j < z →
      (∀ a b t : Fin n,
        a < b → b < t → rank a b t < rank i j z →
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
  exact canonical_feedback_injective_of_ordered_ranked_causality
    A B T n k hCopies FT rank (hCausal T FT)

end DiaryLeafPriority
end ThreeUniformDiaries
