import ThreeUniformDiaries.DiaryOnePassLexRanking
import ThreeUniformDiaries.DiaryPrediaryDefinition

/-!
# Actual finite one-pass event blocks and their original-vertex schedule

The input is an ordered 3-hypergraph on Nat. For each ORIGINAL level m,
we form finite sets of REALISED singleton and ordered-pair germs from
actual leaf vertices above m, group them by their actual old m-type,
and select every child except one default from each parent.

A singleton terminal germ (when m is a leaf) is ALWAYS the default in
its parent: it must have negative bits at every inserted 1-split.
Without a terminal child, choose the lexicographically least normal
child as default by its finite binary word rank. All other normal
children are scheduled in DECREASING original child-rank order.
The separate theorem connecting this order to the final Devlin V3
comparison remains a global transport obligation.

At a source 2-split no new pair events are added; at a source leaf
new singleton events precede that original leaf. All new 2-split
events are before all new 1-split events at each original cut.

The original vertex map is defined by finite sums of event-block
lengths, hence no moving-cut termination argument is required. Its
strict monotonicity and marker fixation are proved below.

No output hyperedge relation, V/E/S completion, global type transport,
or protected flip amalgamation is asserted by these definitions.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- Only actual original leaves at or after m are eligible. -/
noncomputable def realisedOneGerms
    (H : Ordered3Graph Nat) (m : Nat) : Finset (OneGermSpace m) := by
  classical
  exact Finset.univ.filter (fun g =>
    ∃ u : Nat, IsLeaf H u ∧ m ≤ u ∧ oneGermCode H m u = g)

/-- Only actual increasing pairs of original leaves at or after m
are eligible. -/
noncomputable def realisedTwoGerms
    (H : Ordered3Graph Nat) (m : Nat) : Finset (TwoGermSpace m) := by
  classical
  exact Finset.univ.filter (fun g =>
    ∃ u v : Nat, IsLeaf H u ∧ IsLeaf H v ∧
      m ≤ u ∧ u < v ∧ twoGermCode H m u v = g)

/-- Restrict realised singleton germs to a fixed original
singleton parent type. -/
noncomputable def oneGermFibre
    (H : Ordered3Graph Nat) (m : Nat) (parent : OneCodeSpace m) :
    Finset (OneGermSpace m) := by
  classical
  exact (realisedOneGerms H m).filter (fun g => g.1 = parent)

/-- Restrict realised pair germs to a fixed original full
two-type parent. -/
noncomputable def twoGermFibre
    (H : Ordered3Graph Nat) (m : Nat) (parent : TwoCodeSpace m) :
    Finset (TwoGermSpace m) := by
  classical
  exact (realisedTwoGerms H m).filter (fun g => g.1 = parent)

/-- The terminal singleton germ, if present in this parent, is
the default negative child. Otherwise choose the least normal
child by the explicit binary rank of its next-cut source code. -/
noncomputable def oneDefaultGerm
    (H : Ordered3Graph Nat) (m : Nat) (parent : OneCodeSpace m) :
    Option (OneGermSpace m) := by
  classical
  exact if oneGermCode H m m ∈ oneGermFibre H m parent
    then some (oneGermCode H m m)
    else leastOneGermByRank m (oneGermFibre H m parent).toList

/-- Pair children have an arbitrary fixed default. The pair-child
order does not affect the old leaf lexicographic order. -/
noncomputable def twoDefaultGerm
    (H : Ordered3Graph Nat) (m : Nat) (parent : TwoCodeSpace m) :
    Option (TwoGermSpace m) := by
  classical
  exact (twoGermFibre H m parent).toList.head?

/-- Exactly the realised singleton germs other than their
parent's default (one fresh 1-split per selected child). -/
noncomputable def selectedOneGerms
    (H : Ordered3Graph Nat) (m : Nat) : Finset (OneGermSpace m) := by
  classical
  exact (realisedOneGerms H m).filter
    (fun g => some g ≠ oneDefaultGerm H m g.1)

/-- Exactly the realised pair germs other than their
parent's default (one fresh 2-split per selected child). -/
noncomputable def selectedTwoGerms
    (H : Ordered3Graph Nat) (m : Nat) : Finset (TwoGermSpace m) := by
  classical
  exact (realisedTwoGerms H m).filter
    (fun g => some g ≠ twoDefaultGerm H m g.1)

/-- Event vertices record their original cut AND their selected
actual parent-child germ, not merely a synthetic Boolean bit. -/
inductive BlockEvent where
  | pair (m : Nat) (g : TwoGermSpace m)
  | singleton (m : Nat) (g : OneGermSpace m)

/-- Finite events immediately before ORIGINAL vertex m.
The pair events precede the singleton events. No events are
permitted among the distinguished markers 0,1,2. -/
noncomputable def onePassBlock
    (H : Ordered3Graph Nat) (m : Nat) : List BlockEvent := by
  classical
  exact if m < 3 then [] else
    (if IsTwoSplit H m then [] else
      (selectedTwoGerms H m).toList.map (BlockEvent.pair m)) ++
    (if IsLeaf H m then
      (sortOneGermsDescending m
        (selectedOneGerms H m).toList).map (BlockEvent.singleton m)
      else [])

/-- Number of new event vertices before ORIGINAL m. -/
noncomputable def onePassBlockSize
    (H : Ordered3Graph Nat) (m : Nat) : Nat :=
  (onePassBlock H m).length

/-- Start of the event block preceding ORIGINAL m. -/
noncomputable def onePassBefore
    (H : Ordered3Graph Nat) (m : Nat) : Nat :=
  m + ∑ i ∈ Finset.range m, onePassBlockSize H i

/-- The index of ORIGINAL vertex m in the completed enumeration.
Its block is placed before it, not after it. -/
noncomputable def onePassOldImage
    (H : Ordered3Graph Nat) (m : Nat) : Nat :=
  onePassBefore H m + onePassBlockSize H m

theorem terminal_oneGerm_realised
    (H : Ordered3Graph Nat) (m : Nat) (hm : IsLeaf H m) :
    oneGermCode H m m ∈ realisedOneGerms H m := by
  classical
  simp only [realisedOneGerms, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact ⟨m, hm, le_refl m, rfl⟩

theorem terminal_oneGerm_default
    (H : Ordered3Graph Nat) (m : Nat) (hm : IsLeaf H m) :
    oneDefaultGerm H m (oneCode H m m) =
      some (oneGermCode H m m) := by
  classical
  have hmem : oneGermCode H m m ∈
      oneGermFibre H m (oneCode H m m) := by
    simp only [oneGermFibre, Finset.mem_filter]
    exact ⟨terminal_oneGerm_realised H m hm, rfl⟩
  simp [oneDefaultGerm, hmem]

/-- The old terminal leaf m is NEVER selected for a new one-split
at that same original block, even though it belongs to the
parent class. -/
theorem terminal_oneGerm_not_selected
    (H : Ordered3Graph Nat) (m : Nat) (hm : IsLeaf H m) :
    oneGermCode H m m ∉ selectedOneGerms H m := by
  classical
  intro h
  have hNot := (Finset.mem_filter.mp h).2
  have hDefault := terminal_oneGerm_default H m hm
  apply hNot
  simpa only [oneGermCode] using hDefault.symm

@[simp] theorem onePassBlock_markers
    (H : Ordered3Graph Nat) (m : Nat) (hm : m < 3) :
    onePassBlock H m = [] := by
  simp [onePassBlock, hm]

theorem onePassBefore_succ
    (H : Ordered3Graph Nat) (m : Nat) :
    onePassBefore H (m + 1) =
      onePassOldImage H m + 1 := by
  simp [onePassBefore, onePassOldImage, Finset.sum_range_succ]
  omega

theorem onePassOldImage_succ
    (H : Ordered3Graph Nat) (m : Nat) :
    onePassOldImage H (m + 1) =
      onePassOldImage H m + 1 + onePassBlockSize H (m + 1) := by
  calc
    onePassOldImage H (m + 1) =
      onePassBefore H (m + 1) + onePassBlockSize H (m + 1) := rfl
    _ = onePassOldImage H m + 1 + onePassBlockSize H (m + 1) := by
      rw [onePassBefore_succ]

theorem onePassOldImage_strictMono
    (H : Ordered3Graph Nat) :
    StrictMono (onePassOldImage H) := by
  apply strictMono_nat_of_lt_succ
  intro m
  rw [onePassOldImage_succ]
  omega

@[simp] theorem onePassOldImage_zero
    (H : Ordered3Graph Nat) : onePassOldImage H 0 = 0 := by
  simp [onePassOldImage, onePassBefore, onePassBlockSize]

@[simp] theorem onePassOldImage_one
    (H : Ordered3Graph Nat) : onePassOldImage H 1 = 1 := by
  simp [onePassOldImage, onePassBefore, onePassBlockSize,
    Finset.sum_range_succ]

@[simp] theorem onePassOldImage_two
    (H : Ordered3Graph Nat) : onePassOldImage H 2 = 2 := by
  simp [onePassOldImage, onePassBefore, onePassBlockSize,
    Finset.sum_range_succ]

end DiaryLeafPriority
end ThreeUniformDiaries
