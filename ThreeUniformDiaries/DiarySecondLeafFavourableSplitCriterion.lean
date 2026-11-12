import ThreeUniformDiaries.DiarySecondLeafCofinalRootedSplitCriterion

/-!
# Track D: the finite rooted-split criterion for unbounded second-leaf successors

Fix one genuine, already reserved old source stage with precisely ONE
selected source leaf a mapped to a FIXED target leaf w=f(a).
The exact second-leaf fixed-v criterion leaves three inequalities and
one E2 right-bit requirement. For a prescribed exact split s<w, the
verified rooted-split criterion shows that cofinally many successors
exist exactly when the s-fibre is cofinal and its E2 orientation and
two old numerical gaps are correct.

This module ELIMINATES the need to prescribe s in advance.

Every target leaf v>w has a genuine S1 split with w, and that split
lies in the FINITE interval [0,w). Thus if genuine old-compatible
RESERVED second-leaf successors occur at arbitrarily large target
indices, the full successor witnesses have some ONE exact split
s<w occurring cofinally. The verified fixed-split criterion then
forces precisely the three finite E2/gap conditions. Conversely,
one such cofinal favourable s-fibre produces arbitrarily late genuine
reserved second-leaf successors.

This is an exact LOCAL second-leaf classification. It does not assert
the existence of any favourable recurrent s for an arbitrary old root
w, simultaneous third-leaf E3/E5 control, persistence through ALL
finite horizons, or countable-source diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For an already reserved old stage with exactly one genuine source
leaf a, arbitrarily high genuine reserved successors fixing that
old source leaf exist IFF at least ONE target one-split s below the
fixed old image w=f(a) has an unbounded prescribed-range fibre
and passes the required E2 polarity and two finite gap tests.

The prescribed F is not assumed increasing or injective; numerical
cofinality is explicitly part of the condition. All edge/nonedge,
roles, numerical S1/S2 meets, range, and reserve properties are
carried by the existing FULL second-leaf fixed-v equivalence.

This equivalence is not a geometric theorem that supplies a
favourable s; it is an exact diagnosis of that remaining problem. -/
theorem RoleDiary.second_leaf_unbounded_successors_iff_favourable_rooted_split
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (F f : Nat → Nat) (a m : Nat)
    (ha : IsLeaf H a) (hm : IsLeaf H m) (ham : a < m)
    (hOld : countableDiaryLeafPrefix H m = {a})
    (P : ReservedDiaryStage H K F m f)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t)) :
    (∀ M : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
      M < F t ∧
      ReservedDiaryStage H K F (m + 1) g ∧
      (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
        g u = f u) ∧
      g m = F t) ↔
    (∃ s : Nat,
      IsOneSplit K s ∧
      s < f a ∧
      (∀ M : Nat, ∃ t : Nat,
        M < F t ∧ K.oneMeetLevel (f a) (F t) = s) ∧
      (H.edge 0 (H.oneMeetLevel a m) m ↔
        ¬ K.edge 0 s (f a)) ∧
      H.oneMeetLevel a m ≤ s ∧
      s + (a - H.oneMeetLevel a m) ≤ f a) := by
  classical
  let w := f a
  have haPrefix : a ∈ countableDiaryLeafPrefix H m := by
    rw [hOld]
    simp
  have haSupported : a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) a haPrefix
  have hwLeaf : IsLeaf K w := P.1.leaf_role a haSupported ha
  constructor
  · intro hUnbounded
    let R : Nat → Nat → Prop := fun s M =>
      ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        K.oneMeetLevel w (F t) = s ∧
        ReservedDiaryStage H K F (m + 1) g ∧
        (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
          g u = f u) ∧
        g m = F t
    have hDown : ∀ (s M N : Nat),
        N ≤ M → R s M → R s N := by
      intro s M N hNM
      rintro ⟨t,g,hHigh,hMeet,Q,hKeep,hNew⟩
      exact ⟨t,g,lt_of_le_of_lt hNM hHigh,
        hMeet,Q,hKeep,hNew⟩
    have hCover : ∀ M : Nat,
        ∃ s : Nat, s ∈ Finset.range w ∧ R s M := by
      intro M
      obtain ⟨t,g,hHigh,Q,hKeep,hNew⟩ :=
        hUnbounded (max M w)
      have hwLt : w < F t :=
        lt_of_le_of_lt (le_max_right M w) hHigh
      have hsLt : K.oneMeetLevel w (F t) < w :=
        DK.oneMeet_lt_left_of_distinct_leaves w (F t)
          hwLeaf (hFLeaf t) (ne_of_lt hwLt)
      refine ⟨K.oneMeetLevel w (F t),
        Finset.mem_range.mpr hsLt,t,g,?_,rfl,Q,hKeep,hNew⟩
      exact lt_of_le_of_lt (le_max_left M w) hHigh
    obtain ⟨s,hSFinite,hRecur⟩ :=
      finite_choice_persistent_of_downward_type
        (Finset.range w) R hDown hCover
    have hsBelow : s < w := Finset.mem_range.mp hSFinite
    have hCone : ∀ M : Nat, ∃ t : Nat,
        M < F t ∧ K.oneMeetLevel w (F t) = s := by
      intro M
      obtain ⟨t,_g,hHigh,hMeet,_Q,_hKeep,_hNew⟩ := hRecur M
      exact ⟨t,hHigh,hMeet⟩
    have hsRole : IsOneSplit K s := by
      obtain ⟨t,_g,hHigh,hMeet,_Q,_hKeep,_hNew⟩ := hRecur w
      have hRole : IsOneSplit K (K.oneMeetLevel w (F t)) :=
        DK.singleton_meets w (F t) hwLeaf (hFLeaf t)
          (ne_of_lt hHigh)
      simpa only [hMeet] using hRole
    have hAtS : ∀ M : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        K.oneMeetLevel w (F t) = s ∧
        ReservedDiaryStage H K F (m + 1) g ∧
        (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
          g u = f u) ∧
        g m = F t := by
      intro M
      exact hRecur M
    obtain ⟨hBit,hGap1,hGap2⟩ :=
      (DH.second_leaf_rooted_split_cofinal_successor_iff
        DK F f a m s ha hm ham hOld P
        hFLeaf hsRole hsBelow hCone).mp hAtS
    exact ⟨s,hsRole,hsBelow,hCone,hBit,hGap1,hGap2⟩
  · rintro ⟨s,hsRole,hsBelow,hCone,hBit,hGap1,hGap2⟩
    intro M
    obtain ⟨t,g,hHigh,_hMeet,Q,hKeep,hNew⟩ :=
      DH.second_leaf_cofinal_successors_of_rooted_split_fibre
        DK F f a m s ha hm ham hOld P
        hFLeaf hsRole hsBelow hCone hBit hGap1 hGap2 M
    exact ⟨t,g,hHigh,Q,hKeep,hNew⟩

/-- If the fixed old root has arbitrarily late reserved second-leaf
successors, a SINGLE genuine target split s witnesses cofinally many
of them. This strengthens mere existence of an unbounded family of
successors by stabilizing their exact numerical S1 meet with the
OLD fixed leaf. No cofinality of future higher-source stages follows. -/
theorem RoleDiary.second_leaf_unbounded_successors_have_fixed_split
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (F f : Nat → Nat) (a m : Nat)
    (ha : IsLeaf H a) (hm : IsLeaf H m) (ham : a < m)
    (hOld : countableDiaryLeafPrefix H m = {a})
    (P : ReservedDiaryStage H K F m f)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (hUnbounded : ∀ M : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
      M < F t ∧
      ReservedDiaryStage H K F (m + 1) g ∧
      (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
        g u = f u) ∧
      g m = F t) :
    ∃ s : Nat,
      IsOneSplit K s ∧ s < f a ∧
      (∀ M : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        K.oneMeetLevel (f a) (F t) = s ∧
        ReservedDiaryStage H K F (m + 1) g ∧
        (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
          g u = f u) ∧
        g m = F t) := by
  obtain ⟨s,hsRole,hsBelow,hCone,hBit,hGap1,hGap2⟩ :=
    (DH.second_leaf_unbounded_successors_iff_favourable_rooted_split
      DK F f a m ha hm ham hOld P hFLeaf).mp hUnbounded
  refine ⟨s,hsRole,hsBelow,?_⟩
  exact DH.second_leaf_cofinal_successors_of_rooted_split_fibre
    DK F f a m s ha hm ham hOld P
    hFLeaf hsRole hsBelow hCone hBit hGap1 hGap2

end DiaryLeafPriority
end ThreeUniformDiaries
