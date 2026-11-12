import ThreeUniformDiaries.DiaryFiniteSupportProtectedPrefixRanks
import ThreeUniformDiaries.DiaryFiniteLeafMeetCompleteReduct

/-!
# Track B: finite leaf-meet support can retain any complete countable diary prefix

In ANY genuine countable RoleDiary G and for any finite numerical
prefix [0,p), finitely many G leaves and their exact singleton and
full ordered-pair meets generate ALL vertices of this prefix.

Proof: marker vertices are always generated; a genuine leaf generates
itself; a genuine one-split has two witness leaves by V1; and a genuine
two-split has four witness leaves by V2. Each vertex thus has a FINITE
leaf witness set. Taking a maximum of their finite numerical bounds
covers the whole prefix.

The already verified leaf-meet support theorem then extracts an
actual finite full diary from these selected leaves. The elementary
fixed-prefix rank theorem ensures the increasing reindexing literally
preserves every numerical vertex of the chosen prefix.

This is a POSITIVE tool for protected relative absorber constructions.
It is NOT a claim that arbitrary full finite diaries have proper
literal end extensions. The prescribed prefix is of a countable full
diary, not necessarily a full finite diary in isolation.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Finite set of all genuine leaves below a numerical bound. -/
noncomputable def finiteLeavesBefore
    (G : Ordered3Graph Nat) (N : Nat) : Finset Nat := by
  classical
  exact (Finset.range N).filter (IsLeaf G)

/-- A larger numerical cutoff retains every previously selected
genuine leaf. -/
theorem finiteLeavesBefore_mono
    (G : Ordered3Graph Nat) (N M : Nat) (hNM : N ≤ M) :
    finiteLeavesBefore G N ⊆ finiteLeavesBefore G M := by
  classical
  intro u hu
  change u ∈ (Finset.range N).filter (IsLeaf G) at hu
  change u ∈ (Finset.range M).filter (IsLeaf G)
  obtain ⟨huN,hLeaf⟩ := Finset.mem_filter.mp hu
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp huN) hNM),hLeaf⟩

/-- Adding genuine selected leaves can only add generated
singleton-meet and full ordered-pair meet vertices. -/
theorem finiteLeafMeetSupport_mono
    (G : Ordered3Graph Nat)
    {L M : Finset Nat} (hLM : L ⊆ M) :
    finiteLeafMeetSupport G L ⊆ finiteLeafMeetSupport G M := by
  intro x hx
  change x ∈ (Finset.range 3 ∪ L) ∪
      (finiteOneMeetSupport G L ∪ finiteTwoMeetSupport G L) at hx
  rcases Finset.mem_union.mp hx with hFront | hMeets
  · rcases Finset.mem_union.mp hFront with hMarker | hLeaf
    · exact mem_finiteLeafMeetSupport_marker
        G M x (Finset.mem_range.mp hMarker)
    · exact mem_finiteLeafMeetSupport_leaf G M x (hLM hLeaf)
  · rcases Finset.mem_union.mp hMeets with hOne | hTwo
    · obtain ⟨p,hp,hValue⟩ := Finset.mem_image.mp hOne
      rcases p with ⟨a,b⟩
      obtain ⟨hPair,hNe⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hPair
      rw [← hValue]
      exact mem_finiteLeafMeetSupport_oneMeet G M a b
        (hLM ha) (hLM hb) hNe
    · obtain ⟨p,hp,hValue⟩ := Finset.mem_image.mp hTwo
      rcases p with ⟨⟨a,b⟩,⟨c,d⟩⟩
      obtain ⟨hAB,hCD⟩ := Finset.mem_product.mp hp
      obtain ⟨hPairAB,hab⟩ := Finset.mem_filter.mp hAB
      obtain ⟨hPairCD,hcd⟩ := Finset.mem_filter.mp hCD
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hPairAB
      obtain ⟨hc,hd⟩ := Finset.mem_product.mp hPairCD
      rw [← hValue]
      exact mem_finiteLeafMeetSupport_twoMeet G M
        a b c d hab hcd
        (hLM ha) (hLM hb) (hLM hc) (hLM hd)

/-- Every individual vertex of a full countable diary belongs
to a leaf-meet support generated from finitely many actual leaves.
The V1/V2 witness tuples give explicit finite bounds. -/
theorem RoleDiary.exists_leafMeetSupport_containing_vertex
    {G : Ordered3Graph Nat} (D : RoleDiary G)
    (u : Nat) :
    ∃ N : Nat,
      u ∈ finiteLeafMeetSupport G (finiteLeavesBefore G N) := by
  classical
  by_cases huSmall : u < 3
  · exact ⟨0,mem_finiteLeafMeetSupport_marker G
        (finiteLeavesBefore G 0) u huSmall⟩
  · have hu3 : 3 ≤ u := by omega
    rcases D.role_valid u hu3 with hLeaf | hOne | hTwo
    · refine ⟨u+1,?_⟩
      have hMem : u ∈ finiteLeavesBefore G (u+1) := by
        change u ∈ (Finset.range (u+1)).filter (IsLeaf G)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega),hLeaf⟩
      exact mem_finiteLeafMeetSupport_leaf G
        (finiteLeavesBefore G (u+1)) u hMem
    · obtain ⟨a,b,ha,hb,hua,hub,hMeet⟩ :=
        D.one_split_witness u hOne
      let N : Nat := max a b + 1
      have haMem : a ∈ finiteLeavesBefore G N := by
        change a ∈ (Finset.range N).filter (IsLeaf G)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by dsimp [N]; omega),ha⟩
      have hbMem : b ∈ finiteLeavesBefore G N := by
        change b ∈ (Finset.range N).filter (IsLeaf G)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by dsimp [N]; omega),hb⟩
      have hab : a ≠ b := by
        intro hEq
        subst b
        have hSelf := Ordered3Graph.oneMeetLevel_self G a
        omega
      refine ⟨N,?_⟩
      rw [← hMeet]
      exact mem_finiteLeafMeetSupport_oneMeet G
        (finiteLeavesBefore G N) a b haMem hbMem hab
    · obtain ⟨a,b,c,d,hab,hcd,ha,hb,hc,hd,hua,huc,hMeet⟩ :=
        D.two_split_witness u hTwo
      let N : Nat := max (max a b) (max c d) + 1
      have haMem : a ∈ finiteLeavesBefore G N := by
        change a ∈ (Finset.range N).filter (IsLeaf G)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by dsimp [N]; omega),ha⟩
      have hbMem : b ∈ finiteLeavesBefore G N := by
        change b ∈ (Finset.range N).filter (IsLeaf G)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by dsimp [N]; omega),hb⟩
      have hcMem : c ∈ finiteLeavesBefore G N := by
        change c ∈ (Finset.range N).filter (IsLeaf G)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by dsimp [N]; omega),hc⟩
      have hdMem : d ∈ finiteLeavesBefore G N := by
        change d ∈ (Finset.range N).filter (IsLeaf G)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by dsimp [N]; omega),hd⟩
      refine ⟨N,?_⟩
      rw [← hMeet]
      exact mem_finiteLeafMeetSupport_twoMeet G
        (finiteLeavesBefore G N) a b c d hab hcd
        haMem hbMem hcMem hdMem

/-- One finite set of witness leaves generates EVERY vertex
of any prescribed finite numerical prefix of the countable
RoleDiary. The choice of witness bounds is uniformly finite. -/
theorem RoleDiary.exists_leafMeetSupport_covering_prefix
    {G : Ordered3Graph Nat} (D : RoleDiary G)
    (p : Nat) :
    ∃ N : Nat,
      ∀ u : Nat, u < p →
        u ∈ finiteLeafMeetSupport G (finiteLeavesBefore G N) := by
  induction p with
  | zero =>
      exact ⟨0, by intro u hu; omega⟩
  | succ p ih =>
      obtain ⟨N,hOld⟩ := ih
      obtain ⟨M,hNew⟩ :=
        D.exists_leafMeetSupport_containing_vertex p
      let R : Nat := max N M
      have hN : finiteLeavesBefore G N ⊆ finiteLeavesBefore G R :=
        finiteLeavesBefore_mono G N R (le_max_left _ _)
      have hM : finiteLeavesBefore G M ⊆ finiteLeavesBefore G R :=
        finiteLeavesBefore_mono G M R (le_max_right _ _)
      refine ⟨R,?_⟩
      intro u hu
      by_cases hPrev : u < p
      · exact finiteLeafMeetSupport_mono G hN (hOld u hPrev)
      · have huEq : u = p := by omega
        subst u
        exact finiteLeafMeetSupport_mono G hM hNew

/-- A countable full diary admits a GENUINE finite full diary
leaf-meet compression which retains ANY prescribed finite
numerical initial segment LITERALLY under increasing enumeration.
The prefix itself is not assumed to satisfy full finite diary
axioms in isolation, so this does NOT contradict the no-proper-
literal-full-finite-diary-end-extension theorem. -/
theorem RoleDiary.exists_finite_full_diary_retaining_prefix
    {G : Ordered3Graph Nat} (D : RoleDiary G)
    (p : Nat) :
    ∃ L : Finset Nat,
      (∀ u : Nat, u ∈ L → IsLeaf G u) ∧
      FiniteRoleDiaryBlock
        (finiteSupportGraph G (finiteLeafMeetSupport G L))
        (finiteLeafMeetSupport G L).card ∧
      (∀ u : Nat, u < p →
        u < (finiteLeafMeetSupport G L).card ∧
        finiteSupportIndex (finiteLeafMeetSupport G L) u = u) := by
  classical
  obtain ⟨N,hPrefix⟩ := D.exists_leafMeetSupport_covering_prefix p
  let L : Finset Nat := finiteLeavesBefore G N
  have hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u := by
    intro u hu
    change u ∈ (Finset.range N).filter (IsLeaf G) at hu
    exact (Finset.mem_filter.mp hu).2
  have hDiary := finiteLeafMeetSupport_is_finiteDiary D hLeaves
  refine ⟨L,hLeaves,hDiary,?_⟩
  intro u hu
  have hMem : u ∈ finiteLeafMeetSupport G L := hPrefix u hu
  have hSpec := finiteSupportRank_spec
    (finiteLeafMeetSupport G L) u hMem
  have hRank := finiteSupportRank_fixed_prefix
    (finiteLeafMeetSupport G L) p hPrefix u hu
  rw [hRank] at hSpec
  exact ⟨hSpec.1,finiteSupportIndex_fixed_prefix
    (finiteLeafMeetSupport G L) p hPrefix u hu⟩

end DiaryLeafPriority
end ThreeUniformDiaries
