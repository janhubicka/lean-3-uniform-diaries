import ThreeUniformDiaries.DiaryFiniteCanonicalIncreasingSeparation

/-!
# Literal target-edge witnesses for canonical flip-feedback injectivity

An increasing source triple i<j<z in the canonical source pullback
has exactly the incidence of the target flip T at the three image
vertices of the chosen protected map. There is no hidden
type-transport assumption: this follows directly from the actual
definition of finiteDiaryPullbackGraph and finiteDiaryEdgeCode.

Combining that literal identity with the canonical source-code
increasing-triple separation criterion gives an exact GEOMETRIC
collision test. Two distinct canonical source flips must have
a source ordered triple on which their respective chosen protected
maps read opposite edge incidences in the same target flip T.

This is an equivalent test, not an existence theorem for a
universally separating protected-copy family.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- On a strictly increasing source triple, the canonical finite
pullback bit is literally the target's hyperedge incidence at
the three image vertices. -/
theorem finiteDiaryPullback_edgeCode_increasing
    (T : Ordered3Graph Nat) (n : Nat) (f : Nat → Nat)
    (i j z : Fin n) (hij : i < j) (hjz : j < z) :
    finiteDiaryEdgeCode (finiteDiaryPullbackGraph T n f) n i j z =
      decide (T.edge (f i.val) (f j.val) (f z.val)) := by
  change
    decide ((finiteDiaryPullbackGraph T n f).edge
      i.val j.val z.val) =
    decide (T.edge (f i.val) (f j.val) (f z.val))
  rw [finiteDiaryPullbackGraph_edge_iff
    T n f i.val j.val z.val hij hjz z.isLt]

/-- Difference of Boolean decisions is precisely logical
disagreement of the underlying target incidence propositions. -/
theorem decide_ne_iff_not_iff
    (p q : Prop) [Decidable p] [Decidable q] :
    decide p ≠ decide q ↔ ¬ (p ↔ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp,hq]

/-- Canonical geometric feedback is injective iff every pair of
different genuine source flips is witnessed by a strictly
increasing triple whose TWO chosen copies have opposite literal
edge-incidence values in the SAME flipped target. -/
theorem canonical_feedback_injective_iff_literal_target_edge_separation
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
        c ≠ d →
          ∃ i j z : Fin n, i < j ∧ j < z ∧
            ¬ (T.edge
                ((chosenCanonicalSourceFlipMap
                  A B n k hCopies c) i.val)
                ((chosenCanonicalSourceFlipMap
                  A B n k hCopies c) j.val)
                ((chosenCanonicalSourceFlipMap
                  A B n k hCopies c) z.val) ↔
               T.edge
                ((chosenCanonicalSourceFlipMap
                  A B n k hCopies d) i.val)
                ((chosenCanonicalSourceFlipMap
                  A B n k hCopies d) j.val)
                ((chosenCanonicalSourceFlipMap
                  A B n k hCopies d) z.val)) := by
  rw [canonical_feedback_injective_iff_increasing_edge_witness
    A B T n k hCopies FT]
  constructor
  · intro h c d hne
    obtain ⟨i,j,z,hij,hjz,hbit⟩ := h c d hne
    refine ⟨i,j,z,hij,hjz,?_⟩
    have hc := finiteDiaryPullback_edgeCode_increasing
      T n (chosenCanonicalSourceFlipMap A B n k hCopies c)
      i j z hij hjz
    have hd := finiteDiaryPullback_edgeCode_increasing
      T n (chosenCanonicalSourceFlipMap A B n k hCopies d)
      i j z hij hjz
    rw [hc,hd] at hbit
    exact (decide_ne_iff_not_iff _ _).mp hbit
  · intro h c d hne
    obtain ⟨i,j,z,hij,hjz,hdiff⟩ := h c d hne
    refine ⟨i,j,z,hij,hjz,?_⟩
    have hc := finiteDiaryPullback_edgeCode_increasing
      T n (chosenCanonicalSourceFlipMap A B n k hCopies c)
      i j z hij hjz
    have hd := finiteDiaryPullback_edgeCode_increasing
      T n (chosenCanonicalSourceFlipMap A B n k hCopies d)
      i j z hij hjz
    rw [hc,hd]
    exact (decide_ne_iff_not_iff _ _).mpr hdiff

end DiaryLeafPriority
end ThreeUniformDiaries
