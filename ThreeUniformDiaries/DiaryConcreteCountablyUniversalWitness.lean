import ThreeUniformDiaries.DiaryGenericExistenceByPairCode
import ThreeUniformDiaries.CountableGenericEmbedding
import ThreeUniformDiaries.DiaryUpperBoundDirectTransfer
import ThreeUniformDiaries.DiaryExactLabelledBigRamseyDegreeNoGeneric
import ThreeUniformDiaries.DiaryExactUnlabelledBigRamseyDegree

/-!
# Track A: a concrete countably universal 3-hypergraph on Nat

The sharp big Ramsey theorems assume CountablyUniversal U, meaning
every countable ordered 3-hypergraph on Nat admits an induced
UNORDERED embedding into U. The explicit enumerated generic
G constructed from finite Nat-pair pattern codes in #1109
has the finite extension property; the already checked
countable generic embedding theorem gives an induced STRICTLY
INCREASING embedding of every countable graph into this G.

We package that witness and forget the target order, producing
the exact CountablyUniversal predicate of the big Ramsey
theorems. This proves the hypotheses of the terminal upper and
exact-degree theorems are actually inhabited in the library,
not merely logically conditional statements about an
uninstantiated universal structure.

No countable diary unavoidability, flip absorption or
certified Safe fusion is used.
-/

namespace ThreeUniformDiaries

open Ordered3Graph

/-- The explicit Nat-pair-code enumerated generic G is a
COUNTABLY UNIVERSAL unordered 3-hypergraph: it contains an
induced copy of every countable 3-hypergraph on Nat. -/
theorem canonicalGeneric_countablyUniversal :
    CountablyUniversal canonicalGenericEnumerated3Graph.graph := by
  intro H
  obtain ⟨f, hMono, hInduced⟩ :=
    canonicalGenericEnumerated3Graph.exists_countable_induced_embedding H
  let e : Ordered3Graph.Embedding H
      canonicalGenericEnumerated3Graph.graph := {
    toFun := f
    strictMono := hMono
    edge_iff := by
      intro a b c hab hbc
      exact hInduced a b c hab hbc
  }
  exact ⟨e.asUnordered⟩

/-- Countably universal unordered 3-uniform hypergraphs genuinely
exist on Nat, witnessed by the concrete finite-pattern coded G. -/
theorem exists_countablyUniversal_3Graph :
    ∃ U : Ordered3Graph Nat, CountablyUniversal U :=
  ⟨canonicalGenericEnumerated3Graph.graph,
    canonicalGeneric_countablyUniversal⟩

/-- The exact labelled big Ramsey degree formula applies in
particular to the concrete canonical generic 3-hypergraph, not
only to an abstract conditional universal target. -/
theorem canonicalGeneric_exactLabelledBigRamseyDegree
    {a : Nat} (A : EnumNode a) :
    ∃! t : Nat,
      ATRFiniteDecoder.IsLabelledBigRamseyBound
        canonicalGenericEnumerated3Graph.graph A t ∧
      (∀ s : Nat,
        ATRFiniteDecoder.IsLabelledBigRamseyBound
          canonicalGenericEnumerated3Graph.graph A s → t ≤ s) := by
  exact
    ATRFiniteDecoder.exactDiaryCount_is_unique_minimal_labelledBigRamseyBound
      canonicalGenericEnumerated3Graph.graph
      canonicalGeneric_countablyUniversal A

/-- The unlabelled finite-copy version is likewise realised on
the same concrete canonical universal hypergraph. -/
theorem canonicalGeneric_exactUnlabelledBigRamseyDegree
    {a : Nat} (A : EnumNode a) :
    ∃! t : Nat,
      ATRFiniteDecoder.IsUnlabelledBigRamseyBound
        canonicalGenericEnumerated3Graph.graph A t ∧
      (∀ s : Nat,
        ATRFiniteDecoder.IsUnlabelledBigRamseyBound
          canonicalGenericEnumerated3Graph.graph A s → t ≤ s) := by
  exact
    ATRFiniteDecoder.exactUnmarkedDiaryCount_is_unique_minimal_unlabelledBigRamseyBound
      canonicalGenericEnumerated3Graph.graph
      canonicalGeneric_countablyUniversal A

end ThreeUniformDiaries
