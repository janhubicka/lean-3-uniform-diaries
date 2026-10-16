import ThreeUniformDiaries.DiaryOnePassEventTestCensus
import ThreeUniformDiaries.DiaryOnePassBlockCutIntervals

/-!
# Non-leaf original cuts cannot insert singleton type distinctions

The static one-pass schedule inserts a singleton event only before an
ORIGINAL leaf. In particular, a source 1-split m may have new pair
events in B_m, but those are literal TARGET 2-splits and none can
appear as the middle vertex of a singleton edge test.

This file formalizes that fact for the ACTUAL event list and concrete
target relation, not for a synthetic block.

Consequently passing all the events before an old source 1-split or
2-split leaves the singleton-type partition unchanged. Combined
with the original-vertex successor-cut identities, it supplies the
non-leaf cases of the global singleton transport induction.

No assumption on source or target S1/S2 is used.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- There is no selected 1-germ event inside the actual block
before an original NONLEAF vertex, even if B_m has 2-events. -/
theorem onePassBlock_no_singleton_event_of_not_leaf
    (H : Ordered3Graph Nat) (m : Nat)
    (hNotLeaf : ¬ IsLeaf H m)
    (i : Fin (onePassBlock H m).length)
    (g : OneGermSpace m) :
    onePassEventAt H m i ≠ BlockEvent.singleton m g := by
  classical
  intro hget
  have hmem : BlockEvent.singleton m g ∈ onePassBlock H m := by
    have h : onePassEventAt H m i ∈ onePassBlock H m := by
      change (onePassBlock H m).get i ∈ onePassBlock H m
      exact (List.mem_iff_get).mpr ⟨i, rfl⟩
    simpa only [hget] using h
  by_cases hm3 : m < 3
  · simp [onePassBlock, hm3] at hmem
  · by_cases hTwo : IsTwoSplit H m
    · simp [onePassBlock, hm3, hTwo, hNotLeaf] at hmem
    · simp [onePassBlock, hm3, hTwo, hNotLeaf] at hmem

/-- A non-leaf original m may insert pair events but it inserts
NO singleton tests into the target type word through its block. -/
theorem onePassBlock_oneType_unchanged_of_not_leaf
    (P : RolePrediary H) (m u v : Nat)
    (hNotLeaf : ¬ IsLeaf H m) :
    (onePassRawTarget H).SameOneTypeBelow
        (onePassOldImage H m) u v ↔
      (onePassRawTarget H).SameOneTypeBelow
        (onePassBefore H m) u v := by
  rw [onePassBlock_oneType_interval_iff H m u v]
  constructor
  · exact And.left
  · intro hBase
    refine ⟨hBase, ?_⟩
    intro i a ha
    rcases onePass_event_label_at_own_cut H m i with
        ⟨g, hPair⟩ | ⟨g, hOne⟩
    · exact iff_of_false
        (onePassRawTarget_freshTwo_no_one_test P m i g hPair a u)
        (onePassRawTarget_freshTwo_no_one_test P m i g hPair a v)
    · exact False.elim
        (onePassBlock_no_singleton_event_of_not_leaf
          H m hNotLeaf i g hOne)

end DiaryLeafPriority
end ThreeUniformDiaries
