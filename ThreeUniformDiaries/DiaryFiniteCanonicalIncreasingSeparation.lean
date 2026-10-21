import ThreeUniformDiaries.DiaryFiniteCanonicalFeedbackCollisionCheck

/-!
# Genuine increasing-triple witnesses for canonical feedback separation

Raw edge tables have redundant entries at triples that are not
strictly increasing. Canonical codes eliminate those entries.

Consequently distinct canonical source flip codes differ at an
ACTUAL increasing source hyperedge triple, and conversely equality
on these genuine triples forces equality of canonical codes.

The exact finite canonical feedback separation condition can
therefore be checked by a witness triple i<j<k on which the two
pulled-back target incidence bits are different. No dummy or
unordered table coordinate is allowed to serve as a witness.

This is an equivalent finite test for a proposed protected-copy
family, NOT a proof that a coherent family satisfying it exists.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Canonical source flip codes are uniquely determined by their
bits on genuine strictly increasing triples. -/
theorem canonical_source_codes_eq_iff_increasing_bits
    (A : Ordered3Graph Nat) (n : Nat)
    (c d : FiniteDiaryEdgeCode n)
    (hc : c ∈ finiteCanonicalSourceFlipCodes A n)
    (hd : d ∈ finiteCanonicalSourceFlipCodes A n) :
    c = d ↔
      ∀ i j k : Fin n, i < j → j < k →
        c i j k = d i j k := by
  constructor
  · intro h
    subst d
    intro i j k _ _
    rfl
  · intro h
    have hGraph :
        finiteDiaryCodeGraph n c = finiteDiaryCodeGraph n d := by
      apply finiteDiary_graph_ext
      intro a b z
      constructor
      · rintro ⟨ha,hb,hz,hab,hbz,hbit⟩
        refine ⟨ha,hb,hz,hab,hbz,?_⟩
        have hPoint := h ⟨a,ha⟩ ⟨b,hb⟩ ⟨z,hz⟩
          (by exact hab) (by exact hbz)
        exact hPoint ▸ hbit
      · rintro ⟨ha,hb,hz,hab,hbz,hbit⟩
        refine ⟨ha,hb,hz,hab,hbz,?_⟩
        have hPoint := h ⟨a,ha⟩ ⟨b,hb⟩ ⟨z,hz⟩
          (by exact hab) (by exact hbz)
        exact hPoint.symm ▸ hbit
    exact finiteCanonicalSourceFlipCodes_decode_injective
      A n c d hc hd hGraph

/-- Distinct canonical source flips have a genuine increasing
edge bit where they disagree; redundant nonedge-code positions
can never be the only distinction. -/
theorem canonical_source_codes_ne_iff_increasing_witness
    (A : Ordered3Graph Nat) (n : Nat)
    (c d : FiniteDiaryEdgeCode n)
    (hc : c ∈ finiteCanonicalSourceFlipCodes A n)
    (hd : d ∈ finiteCanonicalSourceFlipCodes A n) :
    c ≠ d ↔
      ∃ i j k : Fin n, i < j ∧ j < k ∧
        c i j k ≠ d i j k := by
  classical
  constructor
  · intro hne
    by_contra hnone
    apply hne
    apply (canonical_source_codes_eq_iff_increasing_bits
      A n c d hc hd).mpr
    intro i j k hij hjk
    by_contra hdiff
    exact hnone ⟨i,j,k,hij,hjk,hdiff⟩
  · rintro ⟨i,j,k,_hij,_hjk,hdiff⟩ heq
    exact hdiff (congrFun (congrFun (congrFun heq i) j) k)

/-- The finite canonical geometric-feedback map is injective
precisely when each pair of DISTINCT genuine source flips is
distinguished by a REAL increasing pulled-back hyperedge. -/
theorem canonical_feedback_injective_iff_increasing_edge_witness
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
            finiteDiaryEdgeCode
              (finiteDiaryPullbackGraph T n
                (chosenCanonicalSourceFlipMap
                  A B n k hCopies c)) n i j z ≠
            finiteDiaryEdgeCode
              (finiteDiaryPullbackGraph T n
                (chosenCanonicalSourceFlipMap
                  A B n k hCopies d)) n i j z := by
  let feedback :=
    realizedCanonicalSourceFlipFeedback A B T n k hCopies FT
  constructor
  · intro hinj c d hne
    have hOutputNe : (feedback c).val ≠ (feedback d).val := by
      intro heq
      apply hne
      apply hinj
      exact Subtype.ext heq
    obtain ⟨i,j,z,hij,hjz,hbit⟩ :=
      (canonical_source_codes_ne_iff_increasing_witness
        A n (feedback c).val (feedback d).val
        (feedback c).property (feedback d).property).mp hOutputNe
    refine ⟨i,j,z,hij,hjz,?_⟩
    simpa only [feedback,realizedCanonicalSourceFlipFeedback_val]
      using hbit
  · intro hSeparation c d hEqual
    by_contra hne
    obtain ⟨i,j,z,_hij,_hjz,hbit⟩ := hSeparation c d hne
    have heq := congrArg Subtype.val hEqual
    have hAt := congrFun (congrFun (congrFun heq i) j) z
    apply hbit
    simpa only [feedback,realizedCanonicalSourceFlipFeedback_val]
      using hAt

end DiaryLeafPriority
end ThreeUniformDiaries
