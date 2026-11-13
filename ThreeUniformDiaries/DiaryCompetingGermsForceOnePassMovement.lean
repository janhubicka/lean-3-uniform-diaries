import ThreeUniformDiaries.DiaryOnePassSelectedGermProtectedCut
import ThreeUniformDiaries.DiaryOnePassRealisedClassSeparation
import Lean.Elab.Tactic.Omega

/-!
# Track B: competing realised germ children force one-pass movement

The earlier exact germ-count theorem evaluates how many actual
one-/two-split events one-pass completion inserts at source cut m.
Here is its more geometric consequence, phrased using the genuine
global realised type-germ data rather than selected list membership:

* at an old LEAF level m, two distinct realised ONE-germs with
  the same old parent force a new one-split event at m;
* at a non-TWO-SPLIT level m>=3, two distinct realised TWO-germs
  with the same full old parent force a new two-split event at m.

The proof uses the already checked finite one-hot separation lemma
for children after omitting one default. If NO selected event exists
in that fibre, any two realised children of its parent have the
same zero event-membership vector and must coincide.

Thus any genuinely protected proper cut must have NO such competing
children at its old leaf or non-two-split levels. The conditions
quantify over the entire infinite source's ACTUALLY realised germs,
not merely finite ambient prefixes. This is a necessary obstruction,
not a construction of a relative prediary or an absorbing tower.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- If the selected singleton germ set at m is empty, every
actually realised singleton parent admits at most ONE child germ. -/
theorem realised_oneGerm_parent_unique_of_noSelected
    (H : Ordered3Graph Nat) (m : Nat)
    (hZero : (selectedOneGerms H m).card = 0)
    (g h : OneGermSpace m)
    (hg : g ∈ realisedOneGerms H m)
    (hh : h ∈ realisedOneGerms H m)
    (hParent : g.1 = h.1) :
    g = h := by
  classical
  have hEmpty : selectedOneGerms H m = ∅ :=
    Finset.card_eq_zero.mp hZero
  apply (realised_oneGerm_eq_iff_selected_bits H m g h
    hg hh hParent).mp
  intro c hc
  have hFalse : False := by
    simpa only [hEmpty, Finset.not_mem_empty] using hc
  exact False.elim hFalse

/-- If no selected pair germ exists at m, each realised
full ordered-pair parent has at most ONE child pair germ. -/
theorem realised_twoGerm_parent_unique_of_noSelected
    (H : Ordered3Graph Nat) (m : Nat)
    (hZero : (selectedTwoGerms H m).card = 0)
    (g h : TwoGermSpace m)
    (hg : g ∈ realisedTwoGerms H m)
    (hh : h ∈ realisedTwoGerms H m)
    (hParent : g.1 = h.1) :
    g = h := by
  classical
  have hEmpty : selectedTwoGerms H m = ∅ :=
    Finset.card_eq_zero.mp hZero
  apply (realised_twoGerm_eq_iff_selected_bits H m g h
    hg hh hParent).mp
  intro c hc
  have hFalse : False := by
    simpa only [hEmpty, Finset.not_mem_empty] using hc
  exact False.elim hFalse

/-- TWO different realised one-germ children of the same
old singleton parent at a genuine leaf m force a positive
actual one-pass event block and strict movement of old rank m.
No assumptions about fictitious finitely truncated germ tables. -/
theorem competing_oneGerms_at_leaf_force_oldRank_movement
    (H : Ordered3Graph Nat) (m : Nat)
    (hm3 : 3 ≤ m) (hLeaf : IsLeaf H m)
    (g h : OneGermSpace m)
    (hg : g ∈ realisedOneGerms H m)
    (hh : h ∈ realisedOneGerms H m)
    (hParent : g.1 = h.1)
    (hDiff : g ≠ h) :
    0 < onePassBlockSize H m ∧
      m < onePassOldImage H m := by
  classical
  have hPositive : 0 < (selectedOneGerms H m).card := by
    by_contra hn
    have hZero : (selectedOneGerms H m).card = 0 := by omega
    exact hDiff (realised_oneGerm_parent_unique_of_noSelected
      H m hZero g h hg hh hParent)
  have hCount := onePassBlockSize_eq_selectedGermCounts H m hm3
  change onePassBlockSize H m =
      (if IsTwoSplit H m then 0 else (selectedTwoGerms H m).card) +
      (if IsLeaf H m then (selectedOneGerms H m).card else 0) at hCount
  simp only [if_pos hLeaf] at hCount
  have hBlock : 0 < onePassBlockSize H m := by omega
  exact ⟨hBlock,onePassOldImage_moves_of_nonzeroBlock H m hBlock⟩

/-- TWO distinct actual full ordered-pair germ children with
the same old pair parent at a non-two-split m>=3 force
a genuine pair event block and movement of original rank m. -/
theorem competing_twoGerms_without_twoSplit_force_oldRank_movement
    (H : Ordered3Graph Nat) (m : Nat)
    (hm3 : 3 ≤ m) (hNotTwo : ¬ IsTwoSplit H m)
    (g h : TwoGermSpace m)
    (hg : g ∈ realisedTwoGerms H m)
    (hh : h ∈ realisedTwoGerms H m)
    (hParent : g.1 = h.1)
    (hDiff : g ≠ h) :
    0 < onePassBlockSize H m ∧
      m < onePassOldImage H m := by
  classical
  have hPositive : 0 < (selectedTwoGerms H m).card := by
    by_contra hn
    have hZero : (selectedTwoGerms H m).card = 0 := by omega
    exact hDiff (realised_twoGerm_parent_unique_of_noSelected
      H m hZero g h hg hh hParent)
  have hCount := onePassBlockSize_eq_selectedGermCounts H m hm3
  change onePassBlockSize H m =
      (if IsTwoSplit H m then 0 else (selectedTwoGerms H m).card) +
      (if IsLeaf H m then (selectedOneGerms H m).card else 0) at hCount
  simp only [if_neg hNotTwo] at hCount
  have hBlock : 0 < onePassBlockSize H m := by omega
  exact ⟨hBlock,onePassOldImage_moves_of_nonzeroBlock H m hBlock⟩

end DiaryLeafPriority
end ThreeUniformDiaries
