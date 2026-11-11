import ThreeUniformDiaries.DiaryFixedLeafInfiniteE2Branch
import ThreeUniformDiaries.DiarySecondLeafFixedCandidateConverse

/-!
# Track D: exact rooted split-fibre criterion for an infinite second-leaf tail

Fix a genuine full source and target diary, one already selected source
leaf a and its LITERALLY FIXED target image w=f(a), and the second source
leaf m. The previously checked six-point theorem reduces every proposed
second target leaf v to the RIGHT E2 bit plus three numerical gaps.

Suppose one specific target one-split s<w is realized cofinally as the
exact singleton meet of w with actual later target leaves v in the
prescribed F-range. V1 forces ALL such v to have the same E2 bit at s:
it is exactly the complement of E(0,s,w).

Then there are arbitrarily high RESERVED second-leaf successors at
this SAME s (fixing old source a) if and only if two finite numerical
gaps and the one source/target E2 orientation bit hold. The THIRD gap
can be satisfied by going sufficiently high in the cofinal s-fibre.

This is a conditional but precise rooted extension criterion. The
rooted infinite-branch theorem gives SOME recurrent s for each w; it
DOES NOT guarantee that s satisfies the two fixed gaps or the required
source orientation. No E3/E5 multi-old-leaf conditions or persistence
through all later horizons is inferred.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A cofinal fibre of target leaves with one fixed meet s and a fixed
earlier selected leaf w=f(a) produces arbitrarily high genuine RESERVED
second-source-leaf successors provided the source-right E2 bit is
the complement of E(0,s,w), and the two s/w order-gap tests hold.

The cofinal fibre is explicit and does not follow for a prescribed s
merely from genericity of the leaf-only reduct. -/
theorem RoleDiary.second_leaf_cofinal_successors_of_rooted_split_fibre
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (F f : Nat → Nat) (a m s : Nat)
    (ha : IsLeaf H a) (hm : IsLeaf H m) (ham : a < m)
    (hOld : countableDiaryLeafPrefix H m = {a})
    (P : ReservedDiaryStage H K F m f)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (hsRole : IsOneSplit K s) (hsBelow : s < f a)
    (hCone : ∀ M : Nat, ∃ t : Nat,
      M < F t ∧ K.oneMeetLevel (f a) (F t) = s)
    (hBit : H.edge 0 (H.oneMeetLevel a m) m ↔
      ¬ K.edge 0 s (f a))
    (hGap1 : H.oneMeetLevel a m ≤ s)
    (hGap2 : s + (a - H.oneMeetLevel a m) ≤ f a) :
    ∀ M : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
      M < F t ∧
      K.oneMeetLevel (f a) (F t) = s ∧
      ReservedDiaryStage H K F (m + 1) g ∧
      (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
        g u = f u) ∧
      g m = F t := by
  have haOld : a ∈ countableDiaryLeafPrefix H m := by
    rw [hOld]
    simp
  have haSupported : a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) a haOld
  have hwLeaf : IsLeaf K (f a) :=
    P.1.leaf_role a haSupported ha
  intro M
  obtain ⟨t, hLarge, hMeet⟩ :=
    hCone (max M (f a + (m - a)))
  have hTarget : M < F t := by omega
  have hGap3 : f a + (m - a) ≤ F t := by omega
  have hwLtV : f a < F t := by omega
  have hsLtV : s < F t := lt_trans hsBelow hwLtV
  have hOpp :
      ¬ (K.edge 0 s (f a) ↔ K.edge 0 s (F t)) :=
    DK.oneSplit_witness_opposite_marker s (f a) (F t)
      hsRole hwLeaf (hFLeaf t) hsBelow hsLtV hMeet
  have hRight :
      H.edge 0 (H.oneMeetLevel a m) m ↔
        K.edge 0 (K.oneMeetLevel (f a) (F t)) (F t) := by
    rw [hMeet]
    have hTargetBit :
        (¬ K.edge 0 s (f a)) ↔ K.edge 0 s (F t) := by
      tauto
    exact hBit.trans hTargetBit
  obtain ⟨g,Q,hKeep,hNew⟩ :=
    (DH.second_leaf_fixed_v_reserved_successor_iff
      DK F f a m (F t) ha hm ham hOld P
      (hFLeaf t) ⟨t,rfl⟩).mpr
        ⟨hRight,hGap1,hGap2,hGap3⟩
  exact ⟨t,g,hTarget,hMeet,Q,hKeep,hNew⟩

/-- Exact finite criterion for cofinally many supported second-leaf
successors INSIDE a specified recurrent rooted split fibre s.

The necessity takes any one actual reserved successor and uses the
V1 opposite-branch law to express its right E2 bit in terms of the
FIXED old image w; sufficiency uses cofinal tail selection to meet
the remaining third order-gap. The split s and its cofinality are
genuine assumptions, not constructed at a prescribed old support. -/
theorem RoleDiary.second_leaf_rooted_split_cofinal_successor_iff
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (F f : Nat → Nat) (a m s : Nat)
    (ha : IsLeaf H a) (hm : IsLeaf H m) (ham : a < m)
    (hOld : countableDiaryLeafPrefix H m = {a})
    (P : ReservedDiaryStage H K F m f)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (hsRole : IsOneSplit K s) (hsBelow : s < f a)
    (hCone : ∀ M : Nat, ∃ t : Nat,
      M < F t ∧ K.oneMeetLevel (f a) (F t) = s) :
    (∀ M : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
      M < F t ∧
      K.oneMeetLevel (f a) (F t) = s ∧
      ReservedDiaryStage H K F (m + 1) g ∧
      (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
        g u = f u) ∧
      g m = F t) ↔
    ((H.edge 0 (H.oneMeetLevel a m) m ↔
        ¬ K.edge 0 s (f a)) ∧
      H.oneMeetLevel a m ≤ s ∧
      s + (a - H.oneMeetLevel a m) ≤ f a) := by
  have haOld : a ∈ countableDiaryLeafPrefix H m := by
    rw [hOld]
    simp
  have haSupported : a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) a haOld
  have hwLeaf : IsLeaf K (f a) :=
    P.1.leaf_role a haSupported ha
  constructor
  · intro hAll
    obtain ⟨t,g,hLarge,hMeet,Q,hKeep,hNew⟩ := hAll (f a)
    have hOpp :
        ¬ (K.edge 0 s (f a) ↔ K.edge 0 s (F t)) :=
      DK.oneSplit_witness_opposite_marker s (f a) (F t)
        hsRole hwLeaf (hFLeaf t) hsBelow
        (lt_trans hsBelow hLarge) hMeet
    have hTargetBit :
        K.edge 0 s (F t) ↔ ¬ K.edge 0 s (f a) := by
      tauto
    obtain ⟨hRight,hGap1,hGap2,_hGap3⟩ :=
      (DH.second_leaf_fixed_v_reserved_successor_iff
        DK F f a m (F t) ha hm ham hOld P
        (hFLeaf t) ⟨t,rfl⟩).mp
          ⟨g,Q,hKeep,hNew⟩
    have hRightAtS :
        H.edge 0 (H.oneMeetLevel a m) m ↔
          K.edge 0 s (F t) := by
      simpa only [hMeet] using hRight
    refine ⟨hRightAtS.trans hTargetBit, ?_, ?_⟩
    · simpa only [hMeet] using hGap1
    · simpa only [hMeet] using hGap2
  · rintro ⟨hBit,hGap1,hGap2⟩
    exact DH.second_leaf_cofinal_successors_of_rooted_split_fibre
      DK F f a m s ha hm ham hOld P
      hFLeaf hsRole hsBelow hCone hBit hGap1 hGap2

end DiaryLeafPriority
end ThreeUniformDiaries
