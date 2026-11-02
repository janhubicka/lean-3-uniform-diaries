import ThreeUniformDiaries.DiaryFiniteReservedCandidateCriterion
import ThreeUniformDiaries.DiaryFutureReserveFusion

/-!
# Countable diary embedding from explicit finite-table new-leaf candidates

Combining the exact finite generator-table criterion and the
order-reserved stage fusion theorem yields a direct conditional
statement: if every reserved finite stage at a genuine new source
leaf has SOME candidate target leaf v passing the independently
specified finite table + numerical reserve tests, then a coherent
countable full diary embedding exists.

This does NOT prove existence of such v from finite flip absorption,
leaf-only hypergraph genericity or any target Fraisse property.
The non-circular hypothesis is a concrete statement over the
existing finite generator table, not a reference to a future
infinite path. The quantifier over v is unbounded.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- An explicit finite-table *candidate existence* hypothesis at
new leaves suffices for a complete countable induced diary
embedding, with prescribed leaf range and all numeric meets.

The hypothesis is still the OPEN mathematical gate. It asks for
a target leaf v whose finite generator table passes all tests,
including future order reserve. The theorem makes no claim that
such witnesses are always available. -/
theorem exists_fullDiaryEmbedding_of_reserved_finite_candidates
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H)
    (DK : RoleDiary K)
    (F : Nat → Nat)
    (hCandidate : ∀ m : Nat, IsLeaf H m →
      ∀ f : Nat → Nat,
        ReservedDiaryStage H K F m f →
        ∃ v : Nat,
          FiniteNewLeafCandidateCondition H K F m f v ∧
          FutureOrderReserve H (m + 1)
            (candidateNewLeafTableMap H K m f v)) :
    ∃ e : Ordered3Graph.Embedding H K,
      (∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t) ∧
      (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
        K.oneMeetLevel (e u) (e v) =
          e (H.oneMeetLevel u v)) ∧
      (∀ a b c d : Nat, a < b → c < d →
        3 ≤ a → 3 ≤ c →
        K.twoMeetLevel (e a) (e b) (e c) (e d) =
          e (H.twoMeetLevel a b c d)) := by
  apply exists_fullDiaryEmbedding_of_reserved_new_leaf_extensions DH DK F
  intro m hm f hf
  obtain ⟨v,hFinite⟩ := hCandidate m hm f hf
  obtain ⟨g,hStage,hKeep,hNew,hReserve⟩ :=
    (AdmissibleCofinalDiaryStage.reserved_successor_iff_finite_reserved_candidate
      DH hf.1 hm v).mpr hFinite
  exact ⟨g, ⟨hStage,hReserve⟩, hKeep⟩

end DiaryLeafPriority
end ThreeUniformDiaries
