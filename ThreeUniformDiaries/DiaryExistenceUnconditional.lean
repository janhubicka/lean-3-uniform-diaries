import ThreeUniformDiaries.DiaryShiftedSeedExactLexEarlier
import ThreeUniformDiaries.DiaryExistenceFromShiftedSeed

/-!
# Track B: unconditional countable diary existence with exact ordered leaf reduct

The three-marker seed has now been proved to satisfy the literal V3
LexEarlier comparison, including both capped and proper singleton meets.
The previously verified static one-pass completion then yields a
full countable RoleDiary with EXACTLY the old source leaves, and an
increasing induced source embedding. Both hyperedges and nonedges are
reflected, with no new leaves in the final diary.

No recursive false old-cut lemma, auxiliary Ramsey theorem or countable
unavoidability is used here. The only substantive input beyond the
earlier certified static completion is the genuine numerical V3 theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every enumerated countable ordered 3-hypergraph is the complete,
increasingly enumerated leaf reduct of a full countable diary.
This discharges the explicit seed-V3 premise of the earlier
conditional existence theorem. -/
theorem exists_countable_full_diary_with_exact_leaf_reduct
    (H : Ordered3Graph Nat) :
    ∃ (D : Ordered3Graph Nat),
      RoleDiary D ∧
        ∃ e : Ordered3Graph.Embedding H D,
          (∀ u : Nat, IsLeaf D (e u)) ∧
          (∀ v : Nat, IsLeaf D v → ∃ u : Nat, e u = v) :=
  exists_countable_full_diary_with_exact_leaf_reduct_of_seed_lex H
    (fun a b hab => shiftedDiarySeed_lexEarlier_iff H a b hab)

end DiaryLeafPriority
end ThreeUniformDiaries
