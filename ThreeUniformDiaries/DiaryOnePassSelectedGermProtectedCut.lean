import ThreeUniformDiaries.DiaryOnePassProtectedPrefixEventCriterion
import Lean.Elab.Tactic.Omega

/-!
# Track B: local selected-germ criterion for protecting one-pass prefixes

The exact rank criterion from the previously merged one-pass module
uses the finite lengths of actual inserted event blocks. The
construction, however, chooses such event blocks by looking at
realised ONE- and TWO-germs. We now express their absence directly
in terms of the finite selected-germ sets.

At a nonmarker source position m, a TWO-germ yields an event unless
m already is a 2-split; a ONE-germ yields an event only if m is a
leaf. Thus literal prefix protection amounts exactly to the
absence of these selected germs at each old source cut below p.

This is a precise finite family of conditions on the true global
realised-germ data. It is not a theorem constructing a source
prediary satisfying the conditions while hosting arbitrary strong
absorbers. That positive relative extension remains open.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Selected germ event count, using classical decidability for
the two actual marker-role predicates in this NONCOMPUTABLE
finite counting function. -/
noncomputable def onePassSelectedGermEventCount
    (H : Ordered3Graph Nat) (m : Nat) : Nat := by
  classical
  exact
    (if IsTwoSplit H m then 0 else (selectedTwoGerms H m).card) +
    (if IsLeaf H m then (selectedOneGerms H m).card else 0)

/-- Concrete size of a genuine one-pass event block at a
nonmarker original vertex, expressed directly by its two
finite sets of realised selected successor germs. -/
theorem onePassBlockSize_eq_selectedGermCounts
    (H : Ordered3Graph Nat) (m : Nat) (hm : 3 ≤ m) :
    onePassBlockSize H m = onePassSelectedGermEventCount H m := by
  classical
  change onePassBlockSize H m =
    (if IsTwoSplit H m then 0 else (selectedTwoGerms H m).card) +
    (if IsLeaf H m then (selectedOneGerms H m).card else 0)
  have hNot : ¬ m < 3 := by omega
  by_cases hTwo : IsTwoSplit H m <;>
    by_cases hLeaf : IsLeaf H m <;>
      simp [onePassBlockSize, onePassBlock, hNot, hTwo, hLeaf,
        sortOneGermsDescending_length]

/-- The exact germ-level condition needed to leave every
old rank below the protected cut p untouched in the actual
one-pass completion. Each quantified m has finite germ sets,
although their realisation in H can use arbitrarily late leaves. -/
def OnePassNoSelectedGermsBelow
    (H : Ordered3Graph Nat) (p : Nat) : Prop :=
  ∀ m : Nat, 3 ≤ m → m < p →
    (¬ IsTwoSplit H m → (selectedTwoGerms H m).card = 0) ∧
    (IsLeaf H m → (selectedOneGerms H m).card = 0)

/-- Exact equivalence: no concrete event blocks before p is the
same as absence of the selected pair germs at non-2-split
levels and the selected singleton germs at actual leaf levels. -/
theorem onePassNoEventsBelow_iff_noSelectedGerms
    (H : Ordered3Graph Nat) (p : Nat) :
    OnePassNoEventsBelow H p ↔
      OnePassNoSelectedGermsBelow H p := by
  classical
  constructor
  · intro hNo m hm3 hmp
    have hEq := hNo m hmp
    rw [onePassBlockSize_eq_selectedGermCounts H m hm3] at hEq
    change
      ((if IsTwoSplit H m then 0 else (selectedTwoGerms H m).card) +
        (if IsLeaf H m then (selectedOneGerms H m).card else 0)) = 0 at hEq
    constructor
    · intro hNotTwo
      simp only [if_neg hNotTwo] at hEq
      omega
    · intro hLeaf
      simp only [if_pos hLeaf] at hEq
      omega
  · intro hGerms m hmp
    by_cases hm3 : 3 ≤ m
    · have hLocal := hGerms m hm3 hmp
      have hPair :
          (if IsTwoSplit H m then 0 else
            (selectedTwoGerms H m).card) = 0 := by
        split_ifs with h
        · rfl
        · exact hLocal.1 h
      have hOne :
          (if IsLeaf H m then (selectedOneGerms H m).card
            else 0) = 0 := by
        split_ifs with h
        · exact hLocal.2 h
        · rfl
      rw [onePassBlockSize_eq_selectedGermCounts H m hm3]
      change
        ((if IsTwoSplit H m then 0 else (selectedTwoGerms H m).card) +
          (if IsLeaf H m then (selectedOneGerms H m).card else 0)) = 0
      rw [hPair, hOne]
    · have hSmall : m < 3 := by omega
      simp [onePassBlockSize, onePassBlock, hSmall]

/-- Protected literal rank fixation can be checked directly
against the selected-germ profile, rather than the final
synthetic list of scheduled one-pass events. -/
theorem onePassOldImage_fixed_prefix_iff_noSelectedGerms
    (H : Ordered3Graph Nat) (p : Nat) :
    (∀ m : Nat, m < p → onePassOldImage H m = m) ↔
      OnePassNoSelectedGermsBelow H p :=
  (onePassOldImage_fixed_prefix_iff_noEvents H p).trans
    (onePassNoEventsBelow_iff_noSelectedGerms H p)

end DiaryLeafPriority
end ThreeUniformDiaries
