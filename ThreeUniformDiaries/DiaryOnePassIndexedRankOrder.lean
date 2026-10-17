import ThreeUniformDiaries.DiaryOnePassLexRankSort
import ThreeUniformDiaries.DiaryOnePassPairEventOrder

/-!
# Binary rank order at the ACTUAL one-pass event indices

An original block begins with pair events and ends with singleton
events. We assign pair events rank TOP and real singleton events
their genuine finite binary-germ rank. The existing finite sorting
theorem makes the complete actual event block weakly decreasing in
this extended rank. Consequently, if selected singleton events
appear at concrete Fin indices i<j, the first child has rank at
least that of the second.

The theorem concerns actual onePassEventAt indices and does not
assume target V3 or injectivity on arbitrary raw type codes.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Pair events rank above all singleton events solely to express
the true pair-before-singleton block scheduler in one linear order. -/
def onePassExtendedEventRank : BlockEvent → WithTop Nat
  | .pair _ _ => ⊤
  | .singleton m g => (oneGermBinaryRank m g : WithTop Nat)

/-- A pair prefix followed by a decreasing singleton list is
decreasing in the extended concrete event rank. -/
private theorem onePass_eventRank_pair_prefix
    (m : Nat) (ps : List (TwoGermSpace m))
    (ss : List (OneGermSpace m))
    (hs : ss.Pairwise (fun g h =>
      oneGermBinaryRank m g ≥ oneGermBinaryRank m h)) :
    ((ps.map (BlockEvent.pair m)) ++
      (ss.map (BlockEvent.singleton m))).Pairwise
        (fun x y => onePassExtendedEventRank x ≥
                    onePassExtendedEventRank y) := by
  have hp :
      (ps.map (BlockEvent.pair m)).Pairwise
        (fun x y => onePassExtendedEventRank x ≥
                    onePassExtendedEventRank y) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simp [onePassExtendedEventRank]
  have hss :
      (ss.map (BlockEvent.singleton m)).Pairwise
        (fun x y => onePassExtendedEventRank x ≥
                    onePassExtendedEventRank y) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have hi' : i < ss.length := by simpa using hi
    have hj' : j < ss.length := by simpa using hj
    have hr := (List.pairwise_iff_getElem.mp hs)
      i j hi' hj' hij
    simpa [onePassExtendedEventRank] using hr
  apply List.pairwise_append.mpr
  refine ⟨hp, hss, ?_⟩
  intro x hx y hy
  obtain ⟨g,hg,hEq⟩ := List.mem_map.mp hx
  rw [← hEq]
  simp [onePassExtendedEventRank]

/-- The actual finite event block is weakly decreasing in the
extended rank (pair events are TOP, actual singleton events use
their genuine finite binary ranks). -/
theorem onePassBlock_extended_rank_pairwise
    (H : Ordered3Graph Nat) (m : Nat) :
    (onePassBlock H m).Pairwise
      (fun x y => onePassExtendedEventRank x ≥
                  onePassExtendedEventRank y) := by
  classical
  by_cases hm3 : m < 3
  · simp [onePassBlock, hm3]
  · let ps : List (TwoGermSpace m) :=
      if IsTwoSplit H m then [] else (selectedTwoGerms H m).toList
    let ss : List (OneGermSpace m) :=
      if IsLeaf H m then
        sortOneGermsDescending m (selectedOneGerms H m).toList
      else []
    have hs : ss.Pairwise
        (fun g h => oneGermBinaryRank m g ≥
                    oneGermBinaryRank m h) := by
      by_cases hl : IsLeaf H m
      · simpa [ss, hl] using onePass_selectedOneGerms_pairwise_rank H m
      · simp [ss, hl]
    have h := onePass_eventRank_pair_prefix m ps ss hs
    simpa [onePassBlock, hm3, ps, ss] using h

/-- TRUE positions of selected singleton events in the same
one-pass source block respect decreasing genuine binary rank. -/
theorem onePass_singleton_events_rank_ge_of_index_lt
    (H : Ordered3Graph Nat) (m : Nat)
    (i j : Fin (onePassBlock H m).length)
    (g h : OneGermSpace m)
    (hgi : onePassEventAt H m i = BlockEvent.singleton m g)
    (hhj : onePassEventAt H m j = BlockEvent.singleton m h)
    (hij : i.val < j.val) :
    oneGermBinaryRank m h ≤ oneGermBinaryRank m g := by
  have hr := (onePassBlock_extended_rank_pairwise H m).rel_get_of_lt
    (a := i) (b := j) (by simpa using hij)
  change onePassExtendedEventRank (onePassEventAt H m i) ≥
      onePassExtendedEventRank (onePassEventAt H m j) at hr
  rw [hgi, hhj] at hr
  simpa [onePassExtendedEventRank] using hr

end DiaryLeafPriority
end ThreeUniformDiaries
