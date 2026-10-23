import ThreeUniformDiaries.DiaryFiniteAnchorTableCover
import ThreeUniformDiaries.DiaryFiniteCanonicalSourceFlipOrbit
import ThreeUniformDiaries.DiaryFiniteUnconditionalFlipOrbitBound

/-!
# Exact finite absorption test on CANONICAL target flip codes

The earlier positive-anchor finite table criterion quantified over
raw Boolean edge tables. Multiple raw codes can decode to the SAME
finite target diary because the decoder discards non-increasing
triples. Canonical normalization changes no decoded target graph,
hence changes no positive split-anchor test.

We therefore prove the exact same every-target-flip absorption
criterion with its target quantifier restricted to the FINITE
CANONICAL family of genuine target flips. This family has at most
2^(1+t) members, where t counts genuine two-splits of B,
by the previously verified unconditional fixed-signature theorem.

This is a reduction in the number of relevant target cases for a
given fixed A,B. The canonical finset is classically defined:
nothing here promises a fast executable enumeration or constructs
an absorbing B for an arbitrary A.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Exact positive-anchor covering: check each true finite
target FLIP once, using its unique canonical edge code rather
than all redundant raw codes. Candidate source-flip embedding
tables remain the full canonical set (possibly multiple per
source flip). -/
theorem absorbsEveryTargetFlipInside_iff_canonical_target_anchor_cover
    {A B : Ordered3Graph Nat} {n k : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    AbsorbsEveryTargetFlipInside A B n k ↔
      ∀ tcode : {code : FiniteDiaryEdgeCode k //
          code ∈ finiteCanonicalSourceFlipCodes B k},
        ∃ p : FiniteDiaryEdgeCode n × (Fin n → Fin k),
          p ∈ finiteCanonicalFlipEmbeddingTables A B n k ∧
          FiniteSplitAnchorsPreserved A
            (finiteDiaryCodeGraph k tcode.val) n
            (extendFiniteBoundedMap n k p.2) := by
  rw [absorbsEveryTargetFlipInside_iff_finite_anchor_table_cover DA]
  constructor
  · intro hCover tcode
    have ht : tcode.val ∈ finiteSourceFlipCodes B k :=
      ((mem_finiteCanonicalSourceFlipCodes_iff B k
        tcode.val).mp tcode.property).1
    exact hCover tcode.val ht
  · intro hCover tcode ht
    let T := finiteDiaryCodeGraph k tcode
    let c : FiniteDiaryEdgeCode k := finiteDiaryEdgeCode T k
    have FT : FiniteDiaryFlip B T k :=
      (mem_finiteSourceFlipCodes_iff B k tcode).mp ht
    have hc : c ∈ finiteCanonicalSourceFlipCodes B k :=
      finiteSourceFlipCode_normalized_mem B k tcode ht
    have hDecode : finiteDiaryCodeGraph k c = T :=
      finiteDiaryCodeGraph_reconstruct T k
        FT.target_diary.prediary.frame
    obtain ⟨p,hp,hAnchor⟩ := hCover ⟨c,hc⟩
    refine ⟨p,hp,?_⟩
    simpa only [hDecode] using hAnchor

/-- The number of distinct target cases in this canonical
covering test is at most 2^(1+t), t the number of genuine
two-splits in the FINITE TARGET diary B. There is no source
leaf-count condition, and no assertion that all Boolean bit
vectors are realised. -/
theorem canonical_target_anchor_case_count_bound
    {B : Ordered3Graph Nat} {k : Nat}
    (DB : FiniteRoleDiaryBlock B k) :
    Fintype.card
      {code : FiniteDiaryEdgeCode k //
        code ∈ finiteCanonicalSourceFlipCodes B k} ≤
      2 ^ (finiteTwoSplitCount B k + 1) :=
  finiteCanonicalSourceFlipOrbit_card_bound_unconditional DB

end DiaryLeafPriority
end ThreeUniformDiaries
