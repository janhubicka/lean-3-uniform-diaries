import ThreeUniformDiaries.DiaryOnePassExactFreshRoles

/-!
# Cover all target vertices by old vertices or finite-block events

The static one-pass construction assigns a finite list of new events
before each ORIGINAL vertex m and maps that old vertex to the endpoint
of its block. To establish RolePrediary.role_valid for the entire
target, we must first prove there are NO unnamed target vertices
between the blocks.

We prove coverage by induction on the target index, using the exact
recurrence for onePassBefore and the next old index. This requires
no finite original source or global completion invariant.

We also prove that every actual event label belongs to its original
block cut m and has exactly one of the two specified arities. It is
not a hypothetical event with a different source level.

Neither lemma assumes S1/S2, V1/V2/V3 of the target, or any
synthetic role tags.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every natural-number target index is either one original
vertex or a fresh event with an actual finite-block index. -/
theorem onePass_target_index_covered
    (H : Ordered3Graph Nat) (x : Nat) :
    (∃ m : Nat, onePassOldImage H m = x) ∨
    (∃ m : Nat, ∃ i : Fin (onePassBlock H m).length,
       onePassEventPosition H m i = x) := by
  induction x with
  | zero =>
      exact Or.inl ⟨0, by simp⟩
  | succ x ih =>
      rcases ih with ⟨m, hm⟩ | ⟨m, i, hi⟩
      · by_cases hzero : onePassBlockSize H (m + 1) = 0
        · apply Or.inl
          refine ⟨m + 1, ?_⟩
          have hstep := onePassOldImage_succ H m
          omega
        · have hpositive : 0 < (onePassBlock H (m + 1)).length := by
            dsimp [onePassBlockSize] at hzero
            omega
          apply Or.inr
          refine ⟨m + 1, ⟨0,hpositive⟩, ?_⟩
          have hstep := onePassBefore_succ H m
          dsimp [onePassEventPosition]
          omega
      · have hsize := i.isLt
        by_cases hlast :
            i.val + 1 = (onePassBlock H m).length
        · apply Or.inl
          refine ⟨m, ?_⟩
          dsimp [onePassEventPosition] at hi
          dsimp [onePassOldImage, onePassBlockSize]
          omega
        · have hnext : i.val + 1 < (onePassBlock H m).length := by
            omega
          apply Or.inr
          refine ⟨m, ⟨i.val + 1,hnext⟩, ?_⟩
          dsimp [onePassEventPosition] at hi ⊢
          omega

/-- The label of an actual event in block m can be read only
as a pair or singleton source germ at that SAME cut m. -/
theorem onePass_event_label_at_own_cut
    (H : Ordered3Graph Nat) (m : Nat)
    (i : Fin (onePassBlock H m).length) :
    (∃ g : TwoGermSpace m,
       onePassEventAt H m i = BlockEvent.pair m g) ∨
    (∃ g : OneGermSpace m,
       onePassEventAt H m i = BlockEvent.singleton m g) := by
  classical
  have hmem : onePassEventAt H m i ∈ onePassBlock H m := by
    change (onePassBlock H m).get i ∈ onePassBlock H m
    exact (List.mem_iff_get).mpr ⟨i, rfl⟩
  have hthree : ¬ m < 3 := by
    have h := onePassEvent_cut_ge_three H m i
    omega
  have hNotTwo : ¬ IsTwoSplit H m := by
    intro hTwo
    have hNotLeaf : ¬ IsLeaf H m := by
      intro hLeaf
      exact hLeaf.2.2 hTwo.2.2
    have hEmpty : onePassBlock H m = [] := by
      simp [onePassBlock, hthree, hTwo, hNotLeaf]
    simp [hEmpty] at hmem
  by_cases hLeaf : IsLeaf H m
  · have hparts :
        onePassEventAt H m i ∈
          ((selectedTwoGerms H m).toList.map (BlockEvent.pair m)) ++
          ((sortOneGermsDescending m
            (selectedOneGerms H m).toList).map
            (BlockEvent.singleton m)) := by
        simpa [onePassBlock, hthree, hNotTwo, hLeaf] using hmem
    rcases List.mem_append.mp hparts with hp | hs
    · obtain ⟨g, hg, heq⟩ := List.mem_map.mp hp
      exact Or.inl ⟨g, heq.symm⟩
    · obtain ⟨g, hg, heq⟩ := List.mem_map.mp hs
      exact Or.inr ⟨g, heq.symm⟩
  · have hparts :
        onePassEventAt H m i ∈
          ((selectedTwoGerms H m).toList.map (BlockEvent.pair m)) := by
        simpa [onePassBlock, hthree, hNotTwo, hLeaf] using hmem
    obtain ⟨g, hg, heq⟩ := List.mem_map.mp hparts
    exact Or.inl ⟨g, heq.symm⟩

end DiaryLeafPriority
end ThreeUniformDiaries
