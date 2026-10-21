import ThreeUniformDiaries.DiaryFiniteCanonicalOrderedCausality
import ThreeUniformDiaries.DiaryFiniteCanonicalFlipVariableEdges

/-!
# Only nonleaf incidences need geometric feedback correction

A genuine source diary flip preserves its entire leaf-induced
hypergraph. The canonical feedback for any target flip takes genuine
source flips to genuine source flips. Therefore the canonical
feedback fixes EVERY source leaf-only increasing hyperedge bit,
regardless of the chosen family of protected embeddings or
the target flip. Its XOR correction on these triples is zero.

Consequently the strictly ranked causal feedback condition need be
checked ONLY at genuine increasing triples which contain at least
one nonleaf source vertex. The other triples satisfy the correction
equations automatically, independently of every geometric choice.

This improves the conditional feedback-repair interface without
assuming independent split controls or proving that a suitable
geometric family actually exists.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Actual canonical feedback fixes every source leaf-only
hyperedge bit under EVERY genuine target flip, for ANY chosen
family of protected source-flip embeddings. -/
theorem realizedCanonicalFeedback_leafTriple_fixed
    (A B T : Ordered3Graph Nat) (n k : Nat)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (FT : FiniteDiaryFlip B T k)
    (c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n})
    (i j z : Fin n) (hij : i < j) (hjz : j < z)
    (hi : IsLeaf A i.val) (hj : IsLeaf A j.val)
    (hz : IsLeaf A z.val) :
    (realizedCanonicalSourceFlipFeedback
        A B T n k hCopies FT c).val i j z =
      c.val i j z :=
  canonical_source_flips_agree_on_leaf_triples A n
    (realizedCanonicalSourceFlipFeedback
      A B T n k hCopies FT c).val
    c.val
    (realizedCanonicalSourceFlipFeedback
      A B T n k hCopies FT c).property
    c.property i j z hij hjz hi hj hz

/-- The geometric XOR correction is identically FALSE on
every increasing source leaf triple, regardless of the target
flip, source flip or selected copy. -/
theorem realizedCanonicalFeedback_leafTriple_correction_false
    (A B T : Ordered3Graph Nat) (n k : Nat)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (FT : FiniteDiaryFlip B T k)
    (c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n})
    (i j z : Fin n) (hij : i < j) (hjz : j < z)
    (hi : IsLeaf A i.val) (hj : IsLeaf A j.val)
    (hz : IsLeaf A z.val) :
    Bool.xor
      ((realizedCanonicalSourceFlipFeedback
        A B T n k hCopies FT c).val i j z)
      (c.val i j z) = false := by
  rw [realizedCanonicalFeedback_leafTriple_fixed
    A B T n k hCopies FT c i j z hij hjz hi hj hz]
  cases h : c.val i j z <;> rfl

/-- Ranked prefix causality is sufficient if checked ONLY on
increasing triples containing a nonleaf source vertex.
All-leaf triples need no geometric hypothesis. -/
theorem absorbsEveryTargetFlipInside_of_nonleaf_ranked_causality
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
      (¬ IsLeaf A i.val ∨ ¬ IsLeaf A j.val ∨
        ¬ IsLeaf A z.val) →
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
  classical
  apply absorbsEveryTargetFlipInside_of_ordered_ranked_causality
    A B n k DA hCopies rank
  intro T FT c d i j z hij hjz hPrior
  by_cases hAllLeaf :
      IsLeaf A i.val ∧ IsLeaf A j.val ∧ IsLeaf A z.val
  · have hFirst :=
      realizedCanonicalFeedback_leafTriple_correction_false
        A B T n k hCopies FT c i j z hij hjz
        hAllLeaf.1 hAllLeaf.2.1 hAllLeaf.2.2
    have hSecond :=
      realizedCanonicalFeedback_leafTriple_correction_false
        A B T n k hCopies FT d i j z hij hjz
        hAllLeaf.1 hAllLeaf.2.1 hAllLeaf.2.2
    exact hFirst.trans hSecond.symm
  · have hNonleaf :
        ¬ IsLeaf A i.val ∨ ¬ IsLeaf A j.val ∨
          ¬ IsLeaf A z.val := by
      tauto
    exact hCausal T FT c d i j z hij hjz hNonleaf hPrior

end DiaryLeafPriority
end ThreeUniformDiaries
