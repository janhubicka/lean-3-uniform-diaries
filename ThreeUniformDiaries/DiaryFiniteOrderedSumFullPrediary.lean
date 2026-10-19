import ThreeUniformDiaries.DiaryFiniteOrderedSumGlobalV3
import ThreeUniformDiaries.DiaryFiniteOrderedSumGlobalCoherence
import ThreeUniformDiaries.DiaryFiniteOrderedSumGlobalWitnesses
import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface

/-!
# Complete FINITE ordered-sum V/E pre-diary construction

Given a finite V/E pre-diary H and a finite diary K with all
clauses interpreted on their bounded finite supports, choose one
causal cross-marker orientation. The resulting concrete raw carrier
is a finite V/E pre-diary in the SAME bounded-language sense.

The checked ingredients are now assembled:
* correct finite support and exact three marker roles;
* all five permitted edge shapes E1--E5;
* global V1/V2 positive-class coherence at every actual split;
* a genuinely bounded V1/V2 witness at every target split;
* both literal Devlin V3 marker equivalences for every ordered
  target leaf pair INSIDE the combined finite frame.

S1/S2 need not hold across blocks, so the target is deliberately
a finite PRE-diary, not a finite diary.

The result is NOT a RolePrediary on all Nat: any finite edge
table necessarily lacks Devlin incidences on the infinite
unused tail. Passing from this finite pre-diary to a countable
ambient pre-diary (and ultimately flip absorption) is separate.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- TRUE finite ordered-sum pre-diary theorem. The chosen cross
orientation is a single finite causal Boolean fixed point, and
all target V1/V2 witness leaves are inside the combined bound.
Only the RIGHT input uses S1 (for right-right V3), so the finite
construction can be ITERATED over arbitrarily many diary inputs.
The output is not claimed to satisfy S1/S2. -/
theorem exists_finiteTwoBlock_sum_prediary
    (PH : FiniteRolePrediaryBlock H n)
    (DK : FiniteRoleDiaryBlock K m) :
    ∃ bits : Nat → Bool,
      FiniteRolePrediaryBlock
        (finiteTwoBlockCarrier H K n m bits)
        (finiteTwoBlockLength n m) := by
  let PK := DK.prediary
  obtain ⟨bits,hV3⟩ :=
    exists_finiteTwoBlockOrientation_all_V3
      PH.frame PK.frame PH.permitted_edge PK.permitted_edge
      PH.leaf_marker_one PH.leaf_marker_two
      DK.singleton_meets
      PK.leaf_marker_one PK.leaf_marker_two
  refine ⟨bits, {
    frame := finiteTwoBlockCarrier_finiteFrame
      PH.frame PK.frame bits
    role_valid := ?_
    one_split_coherent := ?_
    one_split_witness := ?_
    two_split_coherent := ?_
    two_split_witness := ?_
    leaf_marker_one := ?_
    leaf_marker_two := ?_
    permitted_edge := ?_
  }⟩
  · intro z hz3 hzBound
    exact finiteTwoBlockCarrier_role_valid
      PH.frame PK.frame PH.role_valid PK.role_valid
      bits z hz3 hzBound
  · intro s a b hs ha hb hA hB
    exact finiteTwoBlockCarrier_oneSplit_coherent
      PH.frame PK.frame PH.one_split_coherent
      PK.permitted_edge PK.one_split_coherent
      bits s a b hs ha hb hA hB
  · intro s hs hsBound
    exact finiteTwoBlockCarrier_oneSplit_bounded_witness
      PH PK bits s hs hsBound
  · intro s a b c d hs hab hcd ha hb hc hd hAB hCD
    exact finiteTwoBlockCarrier_twoSplit_coherent
      PH.frame PK.frame PH.two_split_coherent
      PK.permitted_edge PK.two_split_coherent
      bits s a b c d hs hab hcd ha hb hc hd hAB hCD
  · intro s hs hsBound
    exact finiteTwoBlockCarrier_twoSplit_bounded_witness
      PH PK bits s hs hsBound
  · intro a b hab hbBound ha hb
    exact (hV3 a b hab hbBound ha hb).1
  · intro a b hab hbBound ha hb
    exact (hV3 a b hab hbBound ha hb).2
  · intro x y z he
    exact finiteTwoBlockCarrier_permitted_edge
      PH.frame PK.frame PH.permitted_edge
      PK.permitted_edge bits x y z he

end DiaryLeafPriority
end ThreeUniformDiaries
