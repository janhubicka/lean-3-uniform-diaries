import ThreeUniformDiaries.DiaryFiniteLeafMeetV3
import ThreeUniformDiaries.DiaryFiniteLeafMeetV1Witness
import ThreeUniformDiaries.DiaryFiniteLeafMeetV2Witness
import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface

/-!
# Finite leaf-meet extraction produces a complete finite diary

Let G be a genuine countable RoleDiary, and L any finite set of
genuine leaves. The finite support generated from markers 0,1,2,
selected leaves, their distinct singleton meets and ordered-pair
full meets is a genuine finite RoleDiary block after increasing
induced reindexing.

The theorem assembles only separately checked actual finite
V/E/S clauses: bounded edge frame, genuine marker-defined
roles, both V1/V2 positive coherence and exact bounded split
witnesses, both V3 Devlin marker laws, all E1--E5 edge shapes,
and the complete finite S1/S2 leaf meet alternatives.

It does not claim numerical preservation of arbitrary mixed
tuples under compression, nor does it prove every-flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {G : Ordered3Graph Nat} {L : Finset Nat}

/-- Full finite V/E/S on the increasing induced leaf-meet support
generated from ANY finite set of genuine leaves of a RoleDiary. -/
theorem finiteLeafMeetSupport_is_finiteDiary
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u) :
    FiniteRoleDiaryBlock
      (finiteSupportGraph G (finiteLeafMeetSupport G L))
      (finiteLeafMeetSupport G L).card := by
  classical
  let S := finiteLeafMeetSupport G L
  let H := finiteSupportGraph G S
  have h0 : 0 ∈ S :=
    mem_finiteLeafMeetSupport_marker G L 0 (by omega)
  have h1 : 1 ∈ S :=
    mem_finiteLeafMeetSupport_marker G L 1 (by omega)
  have h2 : 2 ∈ S :=
    mem_finiteLeafMeetSupport_marker G L 2 (by omega)
  refine {
    prediary := {
      frame := finiteSupportGraph_finiteEdgeFrame D h0 h1 h2
      role_valid := ?_
      one_split_coherent := ?_
      one_split_witness := ?_
      two_split_coherent := ?_
      two_split_witness := ?_
      leaf_marker_one := ?_
      leaf_marker_two := ?_
      permitted_edge := ?_
    }
    singleton_meets := ?_
    pair_meets := ?_
  }
  · intro z hz3 hz
    exact finiteLeafMeetSupport_reindexed_role_valid
      D hLeaves z hz3 hz
  · intro s a b hs ha hb hsa hsb
    exact finiteSupportGraph_oneSplit_coherent
      D h0 h1 h2 s a b hs ha hb hsa hsb
  · intro s hs hsBound
    exact finiteLeafMeetSupport_reindexed_oneSplit_witness
      D hLeaves s hs hsBound
  · intro s a b c d hs hab hcd ha hb hc hd hAB hCD
    exact finiteSupportGraph_twoSplit_coherent
      D h0 h1 h2 s a b c d hs hab hcd
      ha hb hc hd hAB hCD
  · intro s hs hsBound
    exact finiteLeafMeetSupport_reindexed_twoSplit_witness
      D hLeaves s hs hsBound
  · intro a b hab hb haLeaf hbLeaf
    exact (finiteLeafMeetSupport_reindexed_V3
      D hLeaves a b hab hb haLeaf hbLeaf).1
  · intro a b hab hb haLeaf hbLeaf
    exact (finiteLeafMeetSupport_reindexed_V3
      D hLeaves a b hab hb haLeaf hbLeaf).2
  · intro x y z he
    exact finiteSupportGraph_permitted_edge D h0 h1 h2 x y z he
  · intro a b hab hb haLeaf hbLeaf
    have ha : a < S.card := lt_trans hab hb
    exact finiteLeafMeetSupport_reindexed_S1
      D hLeaves a b ha hb hab haLeaf hbLeaf
  · intro a b c d hab hcd hb hd haLeaf hbLeaf hcLeaf hdLeaf
    have ha : a < S.card := by omega
    have hc : c < S.card := lt_trans hcd hd
    exact finiteLeafMeetSupport_reindexed_S2
      D hLeaves a b c d ha hb hc hd hab hcd
      haLeaf hbLeaf hcLeaf hdLeaf

end DiaryLeafPriority
end ThreeUniformDiaries
