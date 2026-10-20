import ThreeUniformDiaries.DiaryFiniteLeafMeetReindexedRoles
import ThreeUniformDiaries.DiaryFiniteLeafMeetS2Reduct

/-!
# Genuine bounded V2 witnesses in finite leaf-meet extractions

Each actual two-split in the selected support is a generated
full meet of two ordered selected leaf pairs. The four selected
leaves and their common two-split all survive the increasing
finite reindexing. The retained auxiliary split incidence then
makes their compressed full meet EXACTLY the split index.

This proves existence of actual bounded witnesses for every
two-split of the reindexed reduct, independently of any target
V1/V2 coherence or V3 assertions.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {G : Ordered3Graph Nat} {L : Finset Nat}

/-- Every actual finite two-split has a fully bounded V2 witness
among the selected leaves, with exact compressed pair meet. -/
theorem finiteLeafMeetSupport_reindexed_twoSplit_witness
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    (k : Nat)
    (hSplit : IsTwoSplit
      (finiteSupportGraph G (finiteLeafMeetSupport G L)) k)
    (hk : k < (finiteLeafMeetSupport G L).card) :
    ∃ i j p q : Nat,
      i < j ∧ p < q ∧
      i < (finiteLeafMeetSupport G L).card ∧
      j < (finiteLeafMeetSupport G L).card ∧
      p < (finiteLeafMeetSupport G L).card ∧
      q < (finiteLeafMeetSupport G L).card ∧
      IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) i ∧
      IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) j ∧
      IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) p ∧
      IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) q ∧
      k < i ∧ k < p ∧
      (finiteSupportGraph G (finiteLeafMeetSupport G L)).twoMeetLevel
        i j p q = k := by
  classical
  let S := finiteLeafMeetSupport G L
  let H := finiteSupportGraph G S
  have h0 : 0 ∈ S :=
    mem_finiteLeafMeetSupport_marker G L 0 (by omega)
  have h1 : 1 ∈ S :=
    mem_finiteLeafMeetSupport_marker G L 1 (by omega)
  have h2 : 2 ∈ S :=
    mem_finiteLeafMeetSupport_marker G L 2 (by omega)
  have hOldSplit : IsTwoSplit G (finiteSupportIndex S k) :=
    (finiteSupportGraph_twoSplit_iff
      (G := G) (S := S) h0 h1 h2 k hSplit.1 hk).mp hSplit
  have hkMem : finiteSupportIndex S k ∈ S :=
    finiteSupportIndex_mem S k hk
  obtain ⟨a,b,c,d,ha,hb,hc,hd,hab,hcd,hMeet⟩ :=
    finiteLeafMeetSupport_twoSplit_selected_witness
      D hLeaves hkMem hOldSplit
  obtain ⟨i,hi,hIa⟩ := finiteSupportIndex_surjective_on
    S a (mem_finiteLeafMeetSupport_leaf G L a ha)
  obtain ⟨j,hj,hJb⟩ := finiteSupportIndex_surjective_on
    S b (mem_finiteLeafMeetSupport_leaf G L b hb)
  obtain ⟨p,hp,hPc⟩ := finiteSupportIndex_surjective_on
    S c (mem_finiteLeafMeetSupport_leaf G L c hc)
  obtain ⟨q,hq,hQd⟩ := finiteSupportIndex_surjective_on
    S d (mem_finiteLeafMeetSupport_leaf G L d hd)
  have hTargetLeaf (v t : Nat)
      (hv : v ∈ L) (ht : t < S.card)
      (htv : finiteSupportIndex S t = v) : IsLeaf H t := by
    have hOldLeaf : IsLeaf G (finiteSupportIndex S t) := by
      simpa only [htv] using hLeaves v hv
    have ht3 : 3 ≤ t := finiteSupportIndex_ge_three_of_image
      S t h0 h1 h2 ht hOldLeaf.1
    exact (finiteSupportGraph_leaf_iff
      (G := G) (S := S) h0 h1 h2 t ht3 ht).mpr hOldLeaf
  have hLeafI := hTargetLeaf a i ha hi hIa
  have hLeafJ := hTargetLeaf b j hb hj hJb
  have hLeafP := hTargetLeaf c p hc hp hPc
  have hLeafQ := hTargetLeaf d q hd hQd
  have hij : i < j := finiteSupportIndex_lt_of_image_lt
    S i j hi hj (by simpa only [hIa,hJb] using hab)
  have hpq : p < q := finiteSupportIndex_lt_of_image_lt
    S p q hp hq (by simpa only [hPc,hQd] using hcd)
  have hmBound := G.twoMeetLevel_le_min a b c d
  have hleA : finiteSupportIndex S k ≤ a := by
    rw [← hMeet]
    exact hmBound.trans (min_le_left _ _)
  have hleC : finiteSupportIndex S k ≤ c := by
    rw [← hMeet]
    exact hmBound.trans (min_le_right _ _)
  have hma : finiteSupportIndex S k < a := by
    have hne : finiteSupportIndex S k ≠ a := by
      intro heq
      have hSplitA : IsTwoSplit G a := by
        simpa only [heq] using hOldSplit
      exact (hLeaves a ha).2.2 hSplitA.2.2
    omega
  have hmc : finiteSupportIndex S k < c := by
    have hne : finiteSupportIndex S k ≠ c := by
      intro heq
      have hSplitC : IsTwoSplit G c := by
        simpa only [heq] using hOldSplit
      exact (hLeaves c hc).2.2 hSplitC.2.2
    omega
  have hki : k < i := finiteSupportIndex_lt_of_image_lt
    S k i hk hi (by simpa only [hIa] using hma)
  have hkp : k < p := finiteSupportIndex_lt_of_image_lt
    S k p hk hp (by simpa only [hPc] using hmc)
  have hOldMeet :
      G.twoMeetLevel (finiteSupportIndex S i)
        (finiteSupportIndex S j) (finiteSupportIndex S p)
        (finiteSupportIndex S q) = finiteSupportIndex S k := by
    simpa only [hIa,hJb,hPc,hQd] using hMeet
  have hNewMeet : H.twoMeetLevel i j p q = k :=
    finiteSupportGraph_twoMeet_exact_at_retained_twoSplit
      D i j p q k hi hj hp hq hk hij hpq hki hkp
      hOldSplit hOldMeet
  exact ⟨i,j,p,q,hij,hpq,hi,hj,hp,hq,
    hLeafI,hLeafJ,hLeafP,hLeafQ,hki,hkp,hNewMeet⟩

end DiaryLeafPriority
end ThreeUniformDiaries
