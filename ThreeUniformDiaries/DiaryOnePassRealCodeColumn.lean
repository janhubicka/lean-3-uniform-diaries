import ThreeUniformDiaries.DiaryOnePassLexRanking
import ThreeUniformDiaries.DiaryOnePassCodeEquivalence

/-!
# Decomposing genuine finite singleton codes into old tests and new column

For a realised singleton code over the successor cut m+1, the
lexicographically ordered bit word is precisely the m-prefix of
earlier valid edge tests, followed by the m new tests (q,m,u),
q=0,...,m-1. This is NOT asserted for unnormalised raw functions:
the actual source `oneCode` sets all invalid coordinates to false.

This file gives a concrete representation of the source word, as
opposed to a synthetic lexicographic predicate or code-order axiom.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The actual last column of a genuine normal singleton code.
All tests use the existing (noncomputable) oneCode's Bool values,
so no new decidability hypothesis is added to theorem statements. -/
noncomputable def onePassSourceColumn
    (H : Ordered3Graph Nat) (m u : Nat) : List Bool :=
  (List.finRange m).map (fun a : Fin m =>
    (oneCode H (m + 1) u)
      ⟨a.val, by omega⟩ ⟨m, by omega⟩)

/-- The original singleton code grows by the *last* column of
tests (q,m,u) in increasing q order. -/
theorem onePass_oneCodeBitWord_succ_original
    (H : Ordered3Graph Nat) (m u : Nat) :
    oneCodeBitWord (m + 1) (oneCode H (m + 1) u) =
      oneCodeBitWord m (oneCode H m u) ++
        onePassSourceColumn H m u := by
  classical
  simp [oneCodeBitWord, onePassSourceColumn, oneCode,
    List.finRange_succ_last, List.flatMap_append, List.flatMap_map]

/-- Exact agreement of genuine source types yields equality of
their old prefix bit words. -/
theorem onePass_source_prefix_word_eq
    (H : Ordered3Graph Nat) (m u v : Nat)
    (h : H.SameOneTypeBelow m u v) :
    oneCodeBitWord m (oneCode H m u) =
      oneCodeBitWord m (oneCode H m v) := by
  have hc := (oneCode_eq_iff_sameOneType H m u v).mpr h
  rw [hc]

/-- The q-th bit of a real last-column word is precisely the
actual successor code coordinate (q,m), with q<m. -/
theorem onePass_source_column_bit
    (H : Ordered3Graph Nat) (m u : Nat) (q : Fin m) :
    (onePassSourceColumn H m u)[q.val]'(by
        simp [onePassSourceColumn, q.isLt]) =
      (oneCode H (m + 1) u)
        ⟨q.val, by omega⟩ ⟨m, by omega⟩ := by
  simp [onePassSourceColumn]


end DiaryLeafPriority
end ThreeUniformDiaries
