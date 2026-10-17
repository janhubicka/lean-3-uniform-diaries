import ThreeUniformDiaries.DiaryOnePassSortedGermNodup
import ThreeUniformDiaries.DiaryOnePassEventReflection

/-!
# Uniqueness of EVERY concrete event label inside one-pass blocks

The one-pass schedule consists of a pair-germ list (the toList of an
actual finite set) followed by the descending-rank sorted singleton
germ list. Each list is duplicate-free, and their two event
constructors are disjoint.

We prove the WHOLE actual block list is duplicate-free, and the
function sending an index in that block to its event label is
injective. Consequently a selected singleton/pair germ cannot
appear at any earlier event position with the same label.

This is the finite combinatorial ingredient needed to turn the
already checked positive-vs-default germ child witnesses into
literal target meet witnesses at the selected event vertex.
No source S1/S2 or output diary axiom is used.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The map from source pair germs to their event constructors
is injective for each fixed original level m. -/
private theorem pairEvent_injective (m : Nat) :
    Function.Injective (BlockEvent.pair m) := by
  intro a b heq
  cases heq
  rfl

/-- Likewise for the singleton constructors. -/
private theorem singletonEvent_injective (m : Nat) :
    Function.Injective (BlockEvent.singleton m) := by
  intro a b heq
  cases heq
  rfl

/-- The pair-germ part of every actual block never duplicates
an event label. -/
theorem onePassPairEventList_nodup
    (H : Ordered3Graph Nat) (m : Nat) :
    ((selectedTwoGerms H m).toList.map
      (BlockEvent.pair m)).Nodup := by
  classical
  exact (Finset.nodup_toList _).map (pairEvent_injective m)

/-- Nor does the lex-ranked singleton part. -/
theorem onePassSingletonEventList_nodup
    (H : Ordered3Graph Nat) (m : Nat) :
    ((sortOneGermsDescending m
      (selectedOneGerms H m).toList).map
      (BlockEvent.singleton m)).Nodup := by
  classical
  exact (selectedOneGerms_sorted_nodup H m).map
    (singletonEvent_injective m)

/-- The two arity lists are DISJOINT as lists of concrete event
constructors, independently of all edge or role axioms. -/
theorem onePassPairSingletonLists_disjoint
    (H : Ordered3Graph Nat) (m : Nat) :
    List.Disjoint
      ((selectedTwoGerms H m).toList.map (BlockEvent.pair m))
      ((sortOneGermsDescending m
        (selectedOneGerms H m).toList).map
        (BlockEvent.singleton m)) := by
  intro e hePair heOne
  obtain ⟨g,hg,hgp⟩ := List.mem_map.mp hePair
  obtain ⟨h,hh,hhs⟩ := List.mem_map.mp heOne
  have hImpossible : BlockEvent.pair m g =
      BlockEvent.singleton m h := hgp.trans hhs.symm
  cases hImpossible

/-- No actual original-cut event block repeats ANY event,
not even if one source has infinitely many original leaves. -/
theorem onePassBlock_nodup
    (H : Ordered3Graph Nat) (m : Nat) :
    (onePassBlock H m).Nodup := by
  classical
  have hp := onePassPairEventList_nodup H m
  have hs := onePassSingletonEventList_nodup H m
  have hd := onePassPairSingletonLists_disjoint H m
  have happend :
      (((selectedTwoGerms H m).toList.map (BlockEvent.pair m)) ++
       ((sortOneGermsDescending m
         (selectedOneGerms H m).toList).map
        (BlockEvent.singleton m))).Nodup :=
    hp.append hs hd
  by_cases hm3 : m < 3
  · simp [onePassBlock,hm3]
  · by_cases hTwo : IsTwoSplit H m
    · by_cases hLeaf : IsLeaf H m
      · simpa [onePassBlock,hm3,hTwo,hLeaf] using hs
      · simp [onePassBlock,hm3,hTwo,hLeaf]
    · by_cases hLeaf : IsLeaf H m
      · simpa [onePassBlock,hm3,hTwo,hLeaf] using happend
      · simpa [onePassBlock,hm3,hTwo,hLeaf] using hp

/-- The actual label at a fixed original cut determines its
unique finite-block event index. -/
theorem onePassEventAt_injective
    (H : Ordered3Graph Nat) (m : Nat) :
    Function.Injective (onePassEventAt H m) := by
  intro i j heq
  exact (onePassBlock_nodup H m).injective_get heq

/-- Every EARLIER event of the SAME block has a different
event label, including for singleton children with tied ranks. -/
theorem onePassEventAt_ne_of_lt
    (H : Ordered3Graph Nat) (m : Nat)
    (i j : Fin (onePassBlock H m).length)
    (hji : j.val < i.val) :
    onePassEventAt H m j ≠ onePassEventAt H m i := by
  intro hEq
  have hij : j = i := (onePassEventAt_injective H m) hEq
  have hval := congrArg Fin.val hij
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
