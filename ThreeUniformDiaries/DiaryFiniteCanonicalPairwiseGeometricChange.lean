import ThreeUniformDiaries.DiaryFiniteCanonicalGeometricChange

/-!
# Pairwise geometric synchronization, without a global causal rank

A strictly prefix-causal rank on all genuine hyperedges is a sufficient
condition for canonical feedback injectivity, but may be stronger than
needed: coupling of the genuine source flip coordinates can obstruct a
global triangular presentation.

Here is a different *sufficient* finite geometric criterion. For each
pair of distinct canonical source flips and each target flip, require
only ONE increasing triple whose source incidences differ but whose
B-to-target-flip correction bits on the two selected protected copies
agree. The two feedback incidences at that triple must then differ.

This avoids a common ranking and does not pretend the source flip orbit
is a free Boolean cube. The existence of a target and one compatible
selection of protected copies satisfying the new criterion for ALL
target flips is not proved in this module.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A single *synchronised* geometric change at a genuine source-edge
disagreement suffices to separate that pair after feedback. Requiring
the witness to contain a nonleaf source vertex excludes invariant
leaf-only triples; this is the actual region where distinct genuine
source flips can differ. -/
theorem canonical_feedback_injective_of_pairwise_geometric_change_witness
    (A B T : Ordered3Graph Nat) (n k : Nat)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (FT : FiniteDiaryFlip B T k)
    (hWitness : ∀
      (c d : {code : FiniteDiaryEdgeCode n //
        code ∈ finiteCanonicalSourceFlipCodes A n}),
      c ≠ d →
      ∃ i j z : Fin n,
        i < j ∧ j < z ∧
        (¬ IsLeaf A i.val ∨ ¬ IsLeaf A j.val ∨
          ¬ IsLeaf A z.val) ∧
        c.val i j z ≠ d.val i j z ∧
        canonicalChosenCopyGeometricChange
          A B T n k hCopies c i j z =
        canonicalChosenCopyGeometricChange
          A B T n k hCopies d i j z) :
    Function.Injective
      (realizedCanonicalSourceFlipFeedback
        A B T n k hCopies FT) := by
  classical
  let feedback :=
    realizedCanonicalSourceFlipFeedback A B T n k hCopies FT
  intro c d hFeedback
  by_contra hne
  obtain ⟨i,j,z,hij,hjz,_hNonleaf,hInputNe,hSameChange⟩ :=
    hWitness c d hne
  have hOut : (feedback c).val i j z =
      (feedback d).val i j z := by
    exact congrFun (congrFun
      (congrFun (congrArg Subtype.val hFeedback) i) j) z
  have hCorrectionC :=
    canonicalFeedback_correction_eq_geometricChange
      A B T n k hCopies FT c i j z hij hjz
  have hCorrectionD :=
    canonicalFeedback_correction_eq_geometricChange
      A B T n k hCopies FT d i j z hij hjz
  have hXor :
      Bool.xor ((feedback c).val i j z) (c.val i j z) =
      Bool.xor ((feedback c).val i j z) (d.val i j z) := by
    calc
      Bool.xor ((feedback c).val i j z) (c.val i j z) =
          canonicalChosenCopyGeometricChange
            A B T n k hCopies c i j z := hCorrectionC
      _ = canonicalChosenCopyGeometricChange
            A B T n k hCopies d i j z := hSameChange
      _ = Bool.xor ((feedback d).val i j z) (d.val i j z) :=
          hCorrectionD.symm
      _ = Bool.xor ((feedback c).val i j z) (d.val i j z) := by
          rw [hOut]
  apply hInputNe
  cases hv : (feedback c).val i j z <;>
    cases hc : c.val i j z <;>
    cases hd : d.val i j z <;>
    simp_all [Bool.xor]

/-- Rank-free pairwise synchronization on the chosen protected
source-flip copies, uniformly for EVERY genuine target flip, implies
the strong bounded second flip property. This is conditional on the
geometric witnesses, not an unconditional lower-bound theorem. -/
theorem absorbsEveryTargetFlipInside_of_pairwise_geometric_change_witness
    (A B : Ordered3Graph Nat) (n k : Nat)
    (DA : FiniteRoleDiaryBlock A n)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (hWitness : ∀ (T : Ordered3Graph Nat)
      (FT : FiniteDiaryFlip B T k)
      (c d : {code : FiniteDiaryEdgeCode n //
        code ∈ finiteCanonicalSourceFlipCodes A n}),
      c ≠ d →
      ∃ i j z : Fin n,
        i < j ∧ j < z ∧
        (¬ IsLeaf A i.val ∨ ¬ IsLeaf A j.val ∨
          ¬ IsLeaf A z.val) ∧
        c.val i j z ≠ d.val i j z ∧
        canonicalChosenCopyGeometricChange
          A B T n k hCopies c i j z =
        canonicalChosenCopyGeometricChange
          A B T n k hCopies d i j z) :
    AbsorbsEveryTargetFlipInside A B n k := by
  apply absorbsEveryTargetFlipInside_of_canonical_feedback_injective
    A B n k DA hCopies
  intro T FT
  exact canonical_feedback_injective_of_pairwise_geometric_change_witness
    A B T n k hCopies FT (hWitness T FT)

end DiaryLeafPriority
end ThreeUniformDiaries
