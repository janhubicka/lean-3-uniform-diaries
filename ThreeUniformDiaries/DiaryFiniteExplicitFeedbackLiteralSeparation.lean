import ThreeUniformDiaries.DiaryFiniteExplicitCanonicalFeedback
import ThreeUniformDiaries.DiaryFiniteCanonicalLiteralEdgeSeparation

/-!
# A literal edge-separation criterion for EXPLICIT source-copy feedback

The earlier canonical feedback separation theorem speaks about
Classical.choose maps and therefore cannot be instantiated by
the actual geometric canonical sign-rooted source maps.

Here maps : I -> (Nat -> Nat) is explicit data. If for EVERY pair
of distinct real canonical source flips there is an increasing
source triple on which the SAME flipped target has opposite
edge incidences at their two concrete mapped triples, the
explicit feedback is injective. Finiteness then proves bounded
strong target-flip absorption.

No global causal rank is postulated; a future sign-rooted proof
can provide the distinguishing triple from a first E3 split
or a differing global Devlin marker sign.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Literal pairwise edge separation of the SAME flipped target
through the supplied concrete maps implies injectivity of
explicit canonical feedback. There are no chosen witnesses. -/
theorem explicit_feedback_injective_of_literal_target_separation
    (A B T : Ordered3Graph Nat) (n k : Nat)
    (maps : FiniteCanonicalFlipIndex A n → Nat → Nat)
    (hMaps : ∀ c : FiniteCanonicalFlipIndex A n,
      FiniteBoundedMeetEmbedding
        (finiteDiaryCodeGraph n c.val) B n k (maps c))
    (FT : FiniteDiaryFlip B T k)
    (hSeparate : ∀ c d : FiniteCanonicalFlipIndex A n,
      c ≠ d →
      ∃ i j z : Fin n, i < j ∧ j < z ∧
        ¬ (T.edge (maps c i.val) (maps c j.val) (maps c z.val) ↔
           T.edge (maps d i.val) (maps d j.val) (maps d z.val))) :
    Function.Injective
      (explicitCanonicalSourceFlipFeedback A B T n k maps hMaps FT) := by
  intro c d hFeedback
  by_contra hNe
  obtain ⟨i,j,z,hij,hjz,hDifferent⟩ :=
    hSeparate c d hNe
  have hc := explicitCanonicalSourceFlipFeedback_val
    A B T n k maps hMaps FT c
  have hd := explicitCanonicalSourceFlipFeedback_val
    A B T n k maps hMaps FT d
  have hEqual : finiteDiaryEdgeCode
      (finiteDiaryPullbackGraph T n (maps c)) n i j z =
    finiteDiaryEdgeCode
      (finiteDiaryPullbackGraph T n (maps d)) n i j z := by
    have hVal : (explicitCanonicalSourceFlipFeedback
        A B T n k maps hMaps FT c).val =
      (explicitCanonicalSourceFlipFeedback
        A B T n k maps hMaps FT d).val :=
      congrArg Subtype.val hFeedback
    have hAt := congrFun (congrFun (congrFun hVal i) j) z
    have hci := congrFun (congrFun (congrFun hc i) j) z
    have hdi := congrFun (congrFun (congrFun hd i) j) z
    exact hci.symm.trans (hAt.trans hdi)
  have hBitC := finiteDiaryPullback_edgeCode_increasing
    T n (maps c) i j z hij hjz
  have hBitD := finiteDiaryPullback_edgeCode_increasing
    T n (maps d) i j z hij hjz
  rw [hBitC,hBitD] at hEqual
  exact (finiteTargetEdgeBit_ne_iff_edge_disagreement T
    (maps c i.val) (maps c j.val) (maps c z.val)
    (maps d i.val) (maps d j.val) (maps d z.val)).mpr
      hDifferent hEqual

/-- Actual concrete-copy finite separation for every target
flip implies the STRONG bounded absorption property, without
any change of chosen maps in the permutation argument. -/
theorem absorbsEveryTargetFlipInside_of_explicit_literal_separation
    (A B : Ordered3Graph Nat) (n k : Nat)
    (DA : FiniteRoleDiaryBlock A n)
    (maps : FiniteCanonicalFlipIndex A n → Nat → Nat)
    (hMaps : ∀ c : FiniteCanonicalFlipIndex A n,
      FiniteBoundedMeetEmbedding
        (finiteDiaryCodeGraph n c.val) B n k (maps c))
    (hSeparate : ∀ T : Ordered3Graph Nat,
      ∀ FT : FiniteDiaryFlip B T k,
      ∀ c d : FiniteCanonicalFlipIndex A n,
        c ≠ d →
        ∃ i j z : Fin n, i < j ∧ j < z ∧
          ¬ (T.edge (maps c i.val) (maps c j.val) (maps c z.val) ↔
             T.edge (maps d i.val) (maps d j.val) (maps d z.val))) :
    AbsorbsEveryTargetFlipInside A B n k := by
  apply absorbsEveryTargetFlipInside_of_explicit_feedback_injective
    A B n k DA maps hMaps
  intro T FT
  exact explicit_feedback_injective_of_literal_target_separation
    A B T n k maps hMaps FT (hSeparate T FT)

end DiaryLeafPriority
end ThreeUniformDiaries
