import ThreeUniformDiaries.DiaryOnePassEventReflection
import ThreeUniformDiaries.DiaryOnePassRealisedClassSeparation

/-!
# Every selected original germ is represented by a concrete event vertex

The one-pass source signature proof checks the finite family of selected
germ-class bits. Its relevance to the ACTUAL target depends on showing
that none of those class tests is lost by turning finite sets into
ordered event lists.

We show singleton insertion sort preserves list membership, then that
EVERY selected singleton/pair child occurs as a concrete event in its
original block. Combining this with the exact edge-reflection theorem
produces target-edge tests for each selected class.

This is the event-existence part of the two-way finite-cut transport
proof. Global prefix induction and completed V/E/S remain open.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Decreasing rank insertion changes only the position of a germ,
not whether it occurs in the event list. -/
theorem mem_insertOneGermDescending_iff
    (m : Nat) (g x : OneGermSpace m) (children : List (OneGermSpace m)) :
    x ∈ insertOneGermDescending m g children ↔
      x = g ∨ x ∈ children := by
  induction children with
  | nil =>
    simp [insertOneGermDescending]
  | cons h tail ih =>
    by_cases hr : oneGermBinaryRank m g ≥ oneGermBinaryRank m h
    · simp [insertOneGermDescending, hr, or_assoc]
    · simp [insertOneGermDescending, hr, ih, or_assoc,
        or_left_comm, or_comm]

/-- Sorting never omits any selected source child. -/
theorem mem_sortOneGermsDescending_iff
    (m : Nat) (g : OneGermSpace m) (children : List (OneGermSpace m)) :
    g ∈ sortOneGermsDescending m children ↔ g ∈ children := by
  induction children with
  | nil =>
    simp [sortOneGermsDescending]
  | cons x tail ih =>
    change
      g ∈ insertOneGermDescending m x
        (sortOneGermsDescending m tail) ↔ g ∈ x :: tail
    rw [mem_insertOneGermDescending_iff, ih]
    simp

/-- Each selected singleton type-germ becomes the label of some
actual fresh 1-split in the finite block before old m.
Requires the old vertex m to be a LEAF, as in the one-pass rule. -/
theorem selected_oneGerm_occurs_as_event
    (H : Ordered3Graph Nat) (m : Nat) (hm : IsLeaf H m)
    (g : OneGermSpace m) (hg : g ∈ selectedOneGerms H m) :
    ∃ i : Fin (onePassBlock H m).length,
      onePassEventAt H m i = BlockEvent.singleton m g := by
  classical
  have hm3 : ¬ m < 3 := by omega
  have hlist : g ∈ (selectedOneGerms H m).toList :=
    Finset.mem_toList.mpr hg
  have hsorted : g ∈ sortOneGermsDescending m
      (selectedOneGerms H m).toList :=
    (mem_sortOneGermsDescending_iff m g _).mpr hlist
  have hmapped : BlockEvent.singleton m g ∈
      (sortOneGermsDescending m
        (selectedOneGerms H m).toList).map
          (BlockEvent.singleton m) :=
    List.mem_map.mpr ⟨g, hsorted, rfl⟩
  have hblock : BlockEvent.singleton m g ∈ onePassBlock H m := by
    unfold onePassBlock
    rw [if_neg hm3]
    rw [if_pos hm]
    exact List.mem_append.mpr (Or.inr hmapped)
  obtain ⟨i,hi⟩ := (List.mem_iff_get).mp hblock
  exact ⟨i, hi⟩

/-- Each selected full pair type-germ becomes an actual fresh
2-split in the block before m, whenever the old level is not
already a 2-split. -/
theorem selected_twoGerm_occurs_as_event
    (H : Ordered3Graph Nat) (m : Nat)
    (hm3 : 3 ≤ m) (hNotTwo : ¬ IsTwoSplit H m)
    (g : TwoGermSpace m) (hg : g ∈ selectedTwoGerms H m) :
    ∃ i : Fin (onePassBlock H m).length,
      onePassEventAt H m i = BlockEvent.pair m g := by
  classical
  have hm : ¬ m < 3 := by omega
  have hlist : g ∈ (selectedTwoGerms H m).toList :=
    Finset.mem_toList.mpr hg
  have hmapped : BlockEvent.pair m g ∈
      ((selectedTwoGerms H m).toList.map (BlockEvent.pair m)) :=
    List.mem_map.mpr ⟨g, hlist, rfl⟩
  have hblock : BlockEvent.pair m g ∈ onePassBlock H m := by
    unfold onePassBlock
    rw [if_neg hm, if_neg hNotTwo]
    exact List.mem_append.mpr (Or.inl hmapped)
  obtain ⟨i,hi⟩ := (List.mem_iff_get).mp hblock
  exact ⟨i,hi⟩

/-- Every singleton child bit used by the abstract class separation
lemma is a real, unambiguous target edge test. -/
theorem selected_oneGerm_has_exact_target_edge
    (H : Ordered3Graph Nat) (m u : Nat)
    (hm : IsLeaf H m)
    (g : OneGermSpace m) (hg : g ∈ selectedOneGerms H m) :
    ∃ i : Fin (onePassBlock H m).length,
      onePassEventAt H m i = BlockEvent.singleton m g ∧
      ((onePassRawTarget H).edge 0
        (onePassEventPosition H m i) (onePassOldImage H u) ↔
       IsLeaf H u ∧ m ≤ u ∧ oneGermCode H m u = g) := by
  obtain ⟨i,hi⟩ := selected_oneGerm_occurs_as_event H m hm g hg
  exact ⟨i, hi, onePassRawTarget_singleton_incidence_iff
    H m u i g hi⟩

/-- Likewise every selected full pair child has a real target
test exactly matching its original finite germ (including a cap). -/
theorem selected_twoGerm_has_exact_target_edge
    (H : Ordered3Graph Nat) (m u v : Nat)
    (hm3 : 3 ≤ m) (hNotTwo : ¬ IsTwoSplit H m)
    (g : TwoGermSpace m) (hg : g ∈ selectedTwoGerms H m) :
    ∃ i : Fin (onePassBlock H m).length,
      onePassEventAt H m i = BlockEvent.pair m g ∧
      ((onePassRawTarget H).edge (onePassEventPosition H m i)
        (onePassOldImage H u) (onePassOldImage H v) ↔
        IsLeaf H u ∧ IsLeaf H v ∧ m ≤ u ∧ u < v ∧
          twoGermCode H m u v = g) := by
  obtain ⟨i,hi⟩ :=
    selected_twoGerm_occurs_as_event H m hm3 hNotTwo g hg
  exact ⟨i, hi, onePassRawTarget_pair_incidence_iff
    H m u v i g hi⟩

end DiaryLeafPriority
end ThreeUniformDiaries
