import ThreeUniformDiaries.DiaryFiniteCanonicalE2E3Separation
import ThreeUniformDiaries.DiaryFiniteCanonicalLiteralEdgeSeparation
import ThreeUniformDiaries.DiaryFiniteCanonicalGeometricChange

/-!
# Exact E2/E3 edge tests for canonical geometric feedback

Two canonical finite source flips can differ only on the genuinely
variable E2/E3 one-split and two-split incidences, after the dependent E4
Devlin-marker coordinates are eliminated.

The same is true of the OUTPUTS of canonical feedback: its values
are genuine canonical source flips. Consequently, for an arbitrary
target flip, geometric feedback is injective precisely when every
pair of distinct input codes has a distinguishing literal target
hyperedge among their chosen images of an E2 or E3 source triple.

This is an equivalent finite geometric separation criterion, not
an existence proof for a target or a coherent family of copies.
In particular, it does not assume E2/E3 choices are independent.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Canonical geometric feedback is injective if and ONLY IF
every two distinct actual source flips have their selected
copies separated by the incidence of the SAME flipped target
on an increasing E2 or E3 source triple.

E4 Devlin marker triples are unnecessary even as witnesses
of output disagreement, since their values are determined by
the E2 branch bits of a genuine target pullback flip. -/
theorem canonical_feedback_injective_iff_E2E3_target_edge_separation
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
            IsFiniteFlipE2OrE3Edge A i.val j.val z.val ∧
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
  constructor
  · intro hInjective c d hDifferent
    let feedback :=
      realizedCanonicalSourceFlipFeedback A B T n k hCopies FT
    have hOutputsDifferent :
        (feedback c).val ≠ (feedback d).val := by
      intro hEqual
      apply hDifferent
      apply hInjective
      exact Subtype.ext hEqual
    obtain ⟨i,j,z,hij,hjz,hShape,hBitDifferent⟩ :=
      canonical_source_flips_ne_E2_or_E3_edge_witness
        A n (feedback c).val (feedback d).val
        (feedback c).property (feedback d).property
        hOutputsDifferent
    have hc :=
      canonicalChosenCopy_flipped_edge_bit
        A B T n k hCopies FT c i j z hij hjz
    have hd :=
      canonicalChosenCopy_flipped_edge_bit
        A B T n k hCopies FT d i j z hij hjz
    change (feedback c).val i j z = _ at hc
    change (feedback d).val i j z = _ at hd
    rw [hc,hd] at hBitDifferent
    exact ⟨i,j,z,hij,hjz,hShape,
      (finiteTargetEdgeBit_ne_iff_edge_disagreement T
        ((chosenCanonicalSourceFlipMap A B n k hCopies c) i.val)
        ((chosenCanonicalSourceFlipMap A B n k hCopies c) j.val)
        ((chosenCanonicalSourceFlipMap A B n k hCopies c) z.val)
        ((chosenCanonicalSourceFlipMap A B n k hCopies d) i.val)
        ((chosenCanonicalSourceFlipMap A B n k hCopies d) j.val)
        ((chosenCanonicalSourceFlipMap A B n k hCopies d) z.val)
      ).mp hBitDifferent⟩
  · intro hSeparate
    apply (canonical_feedback_injective_iff_literal_target_edge_separation
      A B T n k hCopies FT).mpr
    intro c d hDifferent
    obtain ⟨i,j,z,hij,hjz,_hShape,hEdgeDifferent⟩ :=
      hSeparate c d hDifferent
    exact ⟨i,j,z,hij,hjz,hEdgeDifferent⟩

/-- Exact finite-geometry route to bounded absorption with
separation witnesses restricted to E2/E3 source triples.
Existence of universally separating protected copies is open. -/
theorem absorbsEveryTargetFlipInside_of_E2E3_target_edge_separation
    (A B : Ordered3Graph Nat) (n k : Nat)
    (DA : FiniteRoleDiaryBlock A n)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (hSeparate : ∀ (T : Ordered3Graph Nat)
      (FT : FiniteDiaryFlip B T k)
      (c d : {code : FiniteDiaryEdgeCode n //
        code ∈ finiteCanonicalSourceFlipCodes A n}),
      c ≠ d →
        ∃ i j z : Fin n, i < j ∧ j < z ∧
          IsFiniteFlipE2OrE3Edge A i.val j.val z.val ∧
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
                 A B n k hCopies d) z.val))) :
    AbsorbsEveryTargetFlipInside A B n k := by
  apply absorbsEveryTargetFlipInside_of_canonical_feedback_injective
    A B n k DA hCopies
  intro T FT
  exact (canonical_feedback_injective_iff_E2E3_target_edge_separation
    A B T n k hCopies FT).mpr (hSeparate T FT)

end DiaryLeafPriority
end ThreeUniformDiaries
