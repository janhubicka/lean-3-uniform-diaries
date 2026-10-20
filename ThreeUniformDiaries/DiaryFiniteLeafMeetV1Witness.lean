import ThreeUniformDiaries.DiaryFiniteLeafMeetReindexedRoles
import ThreeUniformDiaries.DiaryFiniteLeafMeetS1Reduct

/-!
# Actual bounded V1 split witnesses in the finite leaf-meet reduct

Every one-split retained by finite leaf-meet closure was generated
by two distinct selected leaves. Sort those leaves, recover their
finite indices, and invoke the verified retained zero-marker
first-disagreement theorem. The resulting target witnesses are
genuine bounded leaves with exactly the required numerical meet.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {G : Ordered3Graph Nat} {L : Finset Nat}

/-- Singleton first-agreement meets are symmetric without diary
hypotheses; this only uses the symmetry of Boolean equality tests. -/
theorem finiteLeafMeet_oneMeet_comm
    (H : Ordered3Graph Nat) (a b : Nat) :
    H.oneMeetLevel a b = H.oneMeetLevel b a := by
  classical
  have hSym (w : Nat) :
      H.SameOneTypeBelow w a b ↔ H.SameOneTypeBelow w b a := by
    constructor
    · intro h x y hxy hy
      exact (h hxy hy).symm
    · intro h x y hxy hy
      exact (h hxy hy).symm
  have hAB : H.oneMeetLevel a b ≤ min b a := by
    simpa only [min_comm] using H.oneMeetLevel_le_min a b
  have hBA : H.oneMeetLevel b a ≤ min a b := by
    simpa only [min_comm] using H.oneMeetLevel_le_min b a
  have hForward : H.oneMeetLevel a b ≤ H.oneMeetLevel b a :=
    Nat.le_findGreatest hAB
      ((hSym (H.oneMeetLevel a b)).mp (H.oneMeetLevel_agree a b))
  have hBackward : H.oneMeetLevel b a ≤ H.oneMeetLevel a b :=
    Nat.le_findGreatest hBA
      ((hSym (H.oneMeetLevel b a)).mpr (H.oneMeetLevel_agree b a))
  omega

/-- Every selected one-split has actual bounded V1 leaves in the
finite induced diary reduct, witnessing its exact singleton meet. -/
theorem finiteLeafMeetSupport_reindexed_oneSplit_witness
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    (k : Nat)
    (hSplit : IsOneSplit
      (finiteSupportGraph G (finiteLeafMeetSupport G L)) k)
    (hk : k < (finiteLeafMeetSupport G L).card) :
    ∃ i j : Nat,
      i < (finiteLeafMeetSupport G L).card ∧
      j < (finiteLeafMeetSupport G L).card ∧
      IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) i ∧
      IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) j ∧
      k < i ∧ k < j ∧
      (finiteSupportGraph G (finiteLeafMeetSupport G L)).oneMeetLevel i j = k := by
  classical
  let S := finiteLeafMeetSupport G L
  let H := finiteSupportGraph G S
  have h0 : 0 ∈ S :=
    mem_finiteLeafMeetSupport_marker G L 0 (by omega)
  have h1 : 1 ∈ S :=
    mem_finiteLeafMeetSupport_marker G L 1 (by omega)
  have h2 : 2 ∈ S :=
    mem_finiteLeafMeetSupport_marker G L 2 (by omega)
  have hOldSplit : IsOneSplit G (finiteSupportIndex S k) :=
    (finiteSupportGraph_oneSplit_iff
      (G := G) (S := S) h0 h1 h2 k hSplit.1 hk).mp hSplit
  have hkMem : finiteSupportIndex S k ∈ S :=
    finiteSupportIndex_mem S k hk
  obtain ⟨u,v,hu,hv,huv,hMeet⟩ :=
    finiteLeafMeetSupport_oneSplit_selected_witness
      D hLeaves hkMem hOldSplit
  have hSorted : ∃ a b : Nat, a ∈ L ∧ b ∈ L ∧ a < b ∧
      G.oneMeetLevel a b = finiteSupportIndex S k := by
    rcases lt_or_gt_of_ne huv with huvlt | huvgt
    · exact ⟨u,v,hu,hv,huvlt,hMeet⟩
    · refine ⟨v,u,hv,hu,huvgt,?_⟩
      rw [finiteLeafMeet_oneMeet_comm G v u]
      exact hMeet
  obtain ⟨a,b,ha,hb,hab,habMeet⟩ := hSorted
  obtain ⟨i,hi,hIa⟩ := finiteSupportIndex_surjective_on
    S a (mem_finiteLeafMeetSupport_leaf G L a ha)
  obtain ⟨j,hj,hJb⟩ := finiteSupportIndex_surjective_on
    S b (mem_finiteLeafMeetSupport_leaf G L b hb)
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
  have hij : i < j := finiteSupportIndex_lt_of_image_lt
    S i j hi hj (by simpa only [hIa,hJb] using hab)
  have hmBound := G.oneMeetLevel_le_min a b
  have hleA : finiteSupportIndex S k ≤ a := by
    rw [← habMeet]
    exact hmBound.trans (min_le_left _ _)
  have hleB : finiteSupportIndex S k ≤ b := by
    rw [← habMeet]
    exact hmBound.trans (min_le_right _ _)
  have hma : finiteSupportIndex S k < a := by
    have hne : finiteSupportIndex S k ≠ a := by
      intro heq
      have hSplitA : IsOneSplit G a := by
        simpa only [heq] using hOldSplit
      exact (hLeaves a ha).2.1 hSplitA.2.1
    omega
  have hmb : finiteSupportIndex S k < b := by
    have hne : finiteSupportIndex S k ≠ b := by
      intro heq
      have hSplitB : IsOneSplit G b := by
        simpa only [heq] using hOldSplit
      exact (hLeaves b hb).2.1 hSplitB.2.1
    omega
  have hki : k < i := finiteSupportIndex_lt_of_image_lt
    S k i hk hi (by simpa only [hIa] using hma)
  have hkj : k < j := finiteSupportIndex_lt_of_image_lt
    S k j hk hj (by simpa only [hJb] using hmb)
  have hTargetMeet : H.oneMeetLevel i j = k :=
    finiteSupportGraph_oneMeet_exact_at_retained_oneSplit
      D h0 h1 h2 i j k a b (finiteSupportIndex S k)
      hi hj hk hij hSplit.1 hki hkj
      hIa hJb rfl hOldSplit habMeet
  exact ⟨i,j,hi,hj,hLeafI,hLeafJ,hki,hkj,hTargetMeet⟩

end DiaryLeafPriority
end ThreeUniformDiaries
