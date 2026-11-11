import ThreeUniformDiaries.DiaryHighTwoSidedE3RangeWitness
import ThreeUniformDiaries.DiaryProtectedS2FinitePairColour

/-!
# Track D: an infinite high two-sided E3 pair reservoir

The previously verified high E3 theorem selects TWO ordered pairs at
a jointly chosen high two-split. Here the same complete finite full-pair
colour stabilisation is performed once and used to select countably
many mutually separated ordered pairs in the ORIGINAL injective,
possibly unordered, genuine-leaf range.

Every two selected pairs have a genuinely high S2 two-split meet,
and their E3 incidences at THAT meet are opposite. In particular,
the witness supply is pairwise coherent at any fixed finite cut;
it is not merely a sequence of unrelated four-leaf choices.

This is still UNROOTED. Neither any split image nor any branch sign
is prescribed by an old finite diary stage. No reserve, persistent
relative successor, or countable unavoidability is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A countably infinite, input-index-separated list of genuinely
ordered target leaf pairs. Each two DIFFERENT pairs have an exact
S2 two-split meet at or above the prescribed cut B, with opposite
E3 edge/nonedge incidence at that actual meeting split.

The source indices are strictly arranged left-to-right:
  first i < second i < first (i+1).
The prescribed F itself need not be order-preserving, but the two
target leaf values WITHIN each selected pair are increasing.

This theorem does not select E3 signs or target split positions
relative to a previously fixed old support. -/
theorem RoleDiary.exists_infinite_high_E3_pair_reservoir
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (F : Nat → Nat) (hInj : Function.Injective F)
    (hLeaves : ∀ n : Nat, IsLeaf K (F n))
    (B N : Nat) :
    ∃ (first second : Nat → Nat),
      StrictMono first ∧
      (∀ k : Nat,
        N ≤ first k ∧ first k < second k ∧
        second k < first (k + 1) ∧
        F (first k) < F (second k) ∧
        B ≤ F (first k) ∧ B ≤ F (second k)) ∧
      (∀ i j : Nat, i < j →
        ∃ s : Nat,
          B ≤ s ∧ IsTwoSplit K s ∧
          K.twoMeetLevel
            (F (first i)) (F (second i))
            (F (first j)) (F (second j)) = s ∧
          s < F (first i) ∧ s < F (first j) ∧
          ((K.edge s (F (first i)) (F (second i)) ∧
              ¬ K.edge s (F (first j)) (F (second j))) ∨
           (¬ K.edge s (F (first i)) (F (second i)) ∧
              K.edge s (F (first j)) (F (second j))))) := by
  classical
  let T := max B 3
  have hPair (n : Nat) :
      ∃ i j : Nat,
        n ≤ i ∧ i < j ∧ T ≤ F i ∧ T ≤ F j ∧ F i < F j := by
    obtain ⟨M, hM⟩ := injective_nat_eventually_above_bound F hInj T
    let i := max n M
    obtain ⟨L, hL⟩ :=
      injective_nat_eventually_above_bound F hInj (F i)
    let j := max (i + 1) L
    have hni : n ≤ i := by dsimp [i]; omega
    have hMi : M ≤ i := by dsimp [i]; omega
    have hij : i < j := by dsimp [j]; omega
    have hLj : L ≤ j := by dsimp [j]; omega
    have hTi : T < F i := hM i hMi
    have hFij : F i < F j := hL j hLj
    exact ⟨i, j, hni, hij, le_of_lt hTi, by omega, hFij⟩
  let left : Nat → Nat := fun n => Classical.choose (hPair n)
  let right : Nat → Nat :=
    fun n => Classical.choose (Classical.choose_spec (hPair n))
  have hSpec (n : Nat) :
      n ≤ left n ∧ left n < right n ∧
      T ≤ F (left n) ∧ T ≤ F (right n) ∧
      F (left n) < F (right n) := by
    exact Classical.choose_spec (Classical.choose_spec (hPair n))
  let C :=
    ((Fin T → Fin T → Bool) × (Fin T → Fin T → Bool)) ×
      (Fin T → Bool)
  let colour : Nat → C := fun n =>
    fullTwoTypeColour K T (F (left n)) (F (right n))
  let R : C → Nat → Prop := fun c M =>
    ∃ n : Nat, M ≤ n ∧ colour n = c
  have hDown : ∀ (c : C) (n k : Nat),
      k ≤ n → R c n → R c k := by
    intro c n k hkn
    rintro ⟨m, hnm, hColour⟩
    exact ⟨m, hkn.trans hnm, hColour⟩
  have hCover : ∀ n : Nat, ∃ c : C,
      c ∈ (Finset.univ : Finset C) ∧ R c n := by
    intro n
    exact ⟨colour n, Finset.mem_univ _, n, le_rfl, rfl⟩
  obtain ⟨c, _hc, hRecur⟩ :=
    finite_choice_persistent_of_downward_type
      (Finset.univ : Finset C) R hDown hCover
  let pick : Nat → Nat := fun n => Classical.choose (hRecur n)
  have hPick (n : Nat) :
      n ≤ pick n ∧ colour (pick n) = c := by
    exact Classical.choose_spec (hRecur n)
  let pos : Nat → Nat :=
    Nat.rec (pick N) (fun _ prev => pick (right prev + 1))
  have hPosStep (k : Nat) : right (pos k) < pos (k + 1) := by
    change right (pos k) < pick (right (pos k) + 1)
    have h := (hPick (right (pos k) + 1)).1
    omega
  have hLeftStep (k : Nat) :
      left (pos k) < left (pos (k + 1)) := by
    have hOld : left (pos k) < right (pos k) :=
      (hSpec (pos k)).2.1
    have hNew : pos (k + 1) ≤ left (pos (k + 1)) :=
      (hSpec (pos (k + 1))).1
    have hStep := hPosStep k
    omega
  have hLeftMono : StrictMono (fun k => left (pos k)) :=
    strictMono_nat_of_lt_succ hLeftStep
  have hPosLower (k : Nat) : N ≤ pos k := by
    induction k with
    | zero =>
        change N ≤ pick N
        exact (hPick N).1
    | succ k ih =>
        have hOld : pos k ≤ left (pos k) :=
          (hSpec (pos k)).1
        have hPairLt : left (pos k) < right (pos k) :=
          (hSpec (pos k)).2.1
        have hStep := hPosStep k
        omega
  have hColour (k : Nat) : colour (pos k) = c := by
    cases k with
    | zero =>
        change colour (pick N) = c
        exact (hPick N).2
    | succ k =>
        change colour (pick (right (pos k) + 1)) = c
        exact (hPick (right (pos k) + 1)).2
  have hSeparated (i j : Nat) (hij : i < j) :
      right (pos i) < left (pos j) := by
    have hAdj : right (pos i) < left (pos (i + 1)) :=
      lt_of_lt_of_le (hPosStep i) (hSpec (pos (i + 1))).1
    have hRest : left (pos (i + 1)) ≤ left (pos j) :=
      hLeftMono.monotone (Nat.succ_le_of_lt hij)
    exact hAdj.trans_le hRest
  refine ⟨(fun k => left (pos k)), (fun k => right (pos k)),
    hLeftMono, ?_, ?_⟩
  · intro k
    obtain ⟨hFirst, hSecond, hFirstT, hSecondT, hTarget⟩ :=
      hSpec (pos k)
    exact ⟨(hPosLower k).trans hFirst, hSecond,
      hSeparated k (k+1) (Nat.lt_succ_self k),
      hTarget, (le_max_left B 3).trans hFirstT,
      (le_max_left B 3).trans hSecondT⟩
  · intro i j hij
    obtain ⟨_hi, _hij, hTi, _hTib, hab⟩ := hSpec (pos i)
    obtain ⟨_hj, _hjk, hTj, _hTjd, hcd⟩ := hSpec (pos j)
    have hEqual :
        fullTwoTypeColour K T
          (F (left (pos i))) (F (right (pos i))) =
        fullTwoTypeColour K T
          (F (left (pos j))) (F (right (pos j))) :=
      (hColour i).trans (hColour j).symm
    have hSame : K.SameTwoTypeBelow T
        (F (left (pos i))) (F (right (pos i)))
        (F (left (pos j))) (F (right (pos j))) :=
      (fullTwoTypeColour_eq_iff_sameTwoTypeBelow K T
        (F (left (pos i))) (F (right (pos i)))
        (F (left (pos j))) (F (right (pos j)))).mp hEqual
    let s := K.twoMeetLevel
      (F (left (pos i))) (F (right (pos i)))
      (F (left (pos j))) (F (right (pos j)))
    have hHigh : T ≤ s :=
      Nat.le_findGreatest (le_min hTi hTj) hSame
    have hDifferent : F (left (pos i)) ≠ F (left (pos j)) := by
      intro hEq
      have hIndices : left (pos i) = left (pos j) := hInj hEq
      exact (ne_of_lt (hLeftMono hij)) hIndices
    have hTwo : IsTwoSplit K s := by
      rcases DK.pair_meets
        (F (left (pos i))) (F (right (pos i)))
        (F (left (pos j))) (F (right (pos j)))
        hab hcd
        (hLeaves (left (pos i))) (hLeaves (right (pos i)))
        (hLeaves (left (pos j))) (hLeaves (right (pos j))) with
        hCap | hSmall | hSplit
      · have hEq := DK.capped_pair_first_components_equal
          (F (left (pos i))) (F (right (pos i)))
          (F (left (pos j))) (F (right (pos j)))
          hab hcd
          (hLeaves (left (pos i))) (hLeaves (right (pos i)))
          (hLeaves (left (pos j))) (hLeaves (right (pos j)))
          hCap
        exact False.elim (hDifferent hEq)
      · have hT3 : 3 ≤ T := le_max_right B 3
        omega
      · exact hSplit
    have hCap :
        s ≤ min (F (left (pos i))) (F (left (pos j))) :=
      K.twoMeetLevel_le_min
        (F (left (pos i))) (F (right (pos i)))
        (F (left (pos j))) (F (right (pos j)))
    have hNeI : s ≠ F (left (pos i)) := by
      intro hEq
      have hBad : IsTwoSplit K (F (left (pos i))) := hEq ▸ hTwo
      exact (hLeaves (left (pos i))).2.2 hBad.2.2
    have hNeJ : s ≠ F (left (pos j)) := by
      intro hEq
      have hBad : IsTwoSplit K (F (left (pos j))) := hEq ▸ hTwo
      exact (hLeaves (left (pos j))).2.2 hBad.2.2
    have hSi : s < F (left (pos i)) := by
      have h := hCap.trans (min_le_left _ _)
      omega
    have hSj : s < F (left (pos j)) := by
      have h := hCap.trans (min_le_right _ _)
      omega
    have hOpp :
        ¬ (K.edge s (F (left (pos i))) (F (right (pos i))) ↔
          K.edge s (F (left (pos j))) (F (right (pos j)))) :=
      DK.twoSplit_witness_opposite_incidence s
        (F (left (pos i))) (F (right (pos i)))
        (F (left (pos j))) (F (right (pos j)))
        hTwo hSi hSj rfl
    refine ⟨s, (le_max_left B 3).trans hHigh,
      hTwo, rfl, hSi, hSj, ?_⟩
    tauto

end DiaryLeafPriority
end ThreeUniformDiaries
