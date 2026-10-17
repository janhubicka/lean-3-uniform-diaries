import ThreeUniformDiaries.DiaryOnePassFiniteSchedule

/-!
# Rank minimality of the REAL default child in each singleton fibre

A singleton block selects every realised child of a parent except its
default. If a terminal leaf belongs to the fibre, it has rank zero
and is the default. Otherwise the default is the foldl minimum of
all REALISED same-parent germs by finite binary-word numerical rank.

This file proves the actual foldl selector's numeric minimum property.
No injectivity on arbitrary raw Boolean codes, no source S1/S2 and
no target pre-diary condition is postulated here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

private theorem chooseSmallerOneGerm_le_both
    (m : Nat) (x y : OneGermSpace m) :
    ∃ z, chooseSmallerOneGerm m (some x) y = some z ∧
      oneGermBinaryRank m z ≤ oneGermBinaryRank m x ∧
      oneGermBinaryRank m z ≤ oneGermBinaryRank m y := by
  by_cases hlt : oneGermBinaryRank m y < oneGermBinaryRank m x
  · exact ⟨y, by simp [chooseSmallerOneGerm, hlt],
      Nat.le_of_lt hlt, le_rfl⟩
  · exact ⟨x, by simp [chooseSmallerOneGerm, hlt],
      le_rfl, Nat.le_of_not_gt hlt⟩

private theorem chooseSmallerOneGerm_le_new
    (m : Nat) (acc : Option (OneGermSpace m))
    (x : OneGermSpace m) :
    ∃ z, chooseSmallerOneGerm m acc x = some z ∧
      oneGermBinaryRank m z ≤ oneGermBinaryRank m x := by
  cases acc with
  | none =>
      exact ⟨x, rfl, le_rfl⟩
  | some y =>
      obtain ⟨z,hz,_,hzy⟩ := chooseSmallerOneGerm_le_both m y x
      exact ⟨z,hz,hzy⟩

/-- Scanning additional realised children never raises the rank
of an existing nonempty accumulator. -/
theorem onePass_foldlSmaller_le_acc
    (m : Nat) (xs : List (OneGermSpace m))
    (g : OneGermSpace m) :
    ∃ r, xs.foldl (chooseSmallerOneGerm m) (some g) = some r ∧
      oneGermBinaryRank m r ≤ oneGermBinaryRank m g := by
  induction xs generalizing g with
  | nil =>
      exact ⟨g, rfl, le_rfl⟩
  | cons x xs ih =>
      obtain ⟨h,hStep,hLeG,_⟩ :=
        chooseSmallerOneGerm_le_both m g x
      obtain ⟨r,hRest,hLeH⟩ := ih h
      refine ⟨r, ?_, hLeH.trans hLeG⟩
      simpa only [List.foldl_cons, hStep] using hRest

/-- Starting from any accumulator, the foldl minimum has rank
at most that of each element that occurs in the scanned list. -/
theorem onePass_foldlSmaller_le_member
    (m : Nat) (xs : List (OneGermSpace m))
    (acc : Option (OneGermSpace m)) (g : OneGermSpace m)
    (hg : g ∈ xs) :
    ∃ r, xs.foldl (chooseSmallerOneGerm m) acc = some r ∧
      oneGermBinaryRank m r ≤ oneGermBinaryRank m g := by
  induction xs generalizing acc with
  | nil =>
      simp at hg
  | cons x xs ih =>
      rcases List.mem_cons.mp hg with hEq | hTail
      · subst g
        obtain ⟨h,hStep,hLeX⟩ :=
          chooseSmallerOneGerm_le_new m acc x
        obtain ⟨r,hRest,hLeH⟩ :=
          onePass_foldlSmaller_le_acc m xs h
        refine ⟨r, ?_, hLeH.trans hLeX⟩
        simpa only [List.foldl_cons, hStep] using hRest
      · simpa only [List.foldl_cons] using
          ih (chooseSmallerOneGerm m acc x) hTail

/-- The literal finite default selection, without a terminal
override, has rank no larger than any input child. -/
theorem leastOneGermByRank_le_of_mem
    (m : Nat) (xs : List (OneGermSpace m))
    (g : OneGermSpace m) (hg : g ∈ xs) :
    ∃ h, leastOneGermByRank m xs = some h ∧
      oneGermBinaryRank m h ≤ oneGermBinaryRank m g := by
  simpa only [leastOneGermByRank] using
    onePass_foldlSmaller_le_member m xs none g hg

/-- The ACTUAL default in a nonempty realised singleton parent
fibre has minimal rank, whether terminal or normal. -/
theorem oneDefaultGerm_minimal_on_realised_fibre
    (H : Ordered3Graph Nat) (m : Nat) (parent : OneCodeSpace m)
    (h g : OneGermSpace m)
    (hDef : oneDefaultGerm H m parent = some h)
    (hg : g ∈ oneGermFibre H m parent) :
    oneGermBinaryRank m h ≤ oneGermBinaryRank m g := by
  classical
  by_cases ht : oneGermCode H m m ∈ oneGermFibre H m parent
  · have heq : oneGermCode H m m = h := by
      apply Option.some.inj
      simpa [oneDefaultGerm, ht] using hDef
    rw [← heq, terminal_oneGerm_rank_zero]
    exact Nat.zero_le _
  · have hChosen : leastOneGermByRank m
        (oneGermFibre H m parent).toList = some h := by
      simpa [oneDefaultGerm, ht] using hDef
    obtain ⟨k,hk,hLe⟩ := leastOneGermByRank_le_of_mem
      m (oneGermFibre H m parent).toList
      g (Finset.mem_toList.mpr hg)
    rw [hChosen] at hk
    have hEq : h = k := Option.some.inj hk
    simpa only [hEq] using hLe

end DiaryLeafPriority
end ThreeUniformDiaries
