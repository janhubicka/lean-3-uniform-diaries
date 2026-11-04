import ThreeUniformDiaries.DiaryTwoLeafInducedIncidence
import ThreeUniformDiaries.DiarySecondLeafExactOrderReserve
import ThreeUniformDiaries.DiaryNewLeafRightBitAndGaps

/-!
# The full fixed-v criterion at the second selected diary leaf

This is the missing six-coordinate *converse*: after one source leaf
a has been selected, with the next source leaf m>a, an actual target
leaf v in the prescribed range admits a reserved relative successor
fixing the earlier leaf precisely when one mixed E2 orientation bit
matches and the three consecutive future-order gaps hold.

The theorem is about a FIXED v. It does not assert that a suitable v
exists inside an arbitrary prescribed generic leaf copy, and hence
does not establish countable unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

theorem RoleDiary.second_leaf_fixed_v_reserved_successor_iff
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (F f : Nat → Nat) (a m v : Nat)
    (ha : IsLeaf H a) (hm : IsLeaf H m) (ham : a < m)
    (hOld : countableDiaryLeafPrefix H m = {a})
    (P : ReservedDiaryStage H K F m f)
    (hvLeaf : IsLeaf K v)
    (hvRange : ∃ t : Nat, v = F t) :
    (∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1) g ∧
      (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m → g u = f u) ∧
      g m = v) ↔
      ((H.edge 0 (H.oneMeetLevel a m) m ↔
         K.edge 0 (K.oneMeetLevel (f a) v) v) ∧
       H.oneMeetLevel a m ≤ K.oneMeetLevel (f a) v ∧
       K.oneMeetLevel (f a) v + (a - H.oneMeetLevel a m) ≤ f a ∧
       f a + (m - a) ≤ v) := by
  classical
  constructor
  · rintro ⟨g,Q,hKeep,hNew⟩
    have haPrefix : a ∈ countableDiaryLeafPrefix H m := by
      rw [hOld]
      simp
    have hNeeded :=
      reserved_successor_old_new_right_bit_and_three_gaps
        DH hm haPrefix Q hKeep
    rw [hNew] at hNeeded
    exact hNeeded
  · rintro ⟨hBit,hGap1,hGap2,hGap3⟩
    let s := H.oneMeetLevel a m
    let w := f a
    let r := K.oneMeetLevel w v
    have hsRole : IsOneSplit H s :=
      DH.singleton_meets a m ha hm (ne_of_lt ham)
    have hs3 : 3 ≤ s := hsRole.1
    have hsLtA : s < a :=
      DH.oneMeet_lt_left_of_distinct_leaves a m ha hm (ne_of_lt ham)
    have hWltV : w < v := by
      have hd := Nat.sub_pos_of_lt ham
      omega
    have haPrefix : a ∈ countableDiaryLeafPrefix H m := by
      rw [hOld]
      simp
    have haOldSup : a ∈ countableDiaryFiniteSupport H m :=
      mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H m) a haPrefix
    have hwLeaf : IsLeaf K w :=
      P.1.leaf_role a haOldSup ha
    have hrRole : IsOneSplit K r :=
      DK.singleton_meets w v hwLeaf hvLeaf (ne_of_lt hWltV)
    let g : Nat → Nat :=
      fun u => if u = m then v else if u = a then w
        else if u = s then r else u
    have hGM : g m = v := by
      simp [g]
    have hGA : g a = w := by
      simp [g, ne_of_lt ham]
    have hGS : g s = r := by
      have hsm : s ≠ m := ne_of_lt (lt_trans hsLtA ham)
      have hsa : s ≠ a := ne_of_lt hsLtA
      simp [g, hsm, hsa]
    have hMark : ∀ i : Nat, i < 3 → g i = i := by
      intro i hi
      have him : i ≠ m := by omega
      have hia : i ≠ a := by omega
      have his : i ≠ s := by omega
      simp [g,him,hia,his]
    have hNewPrefix :
        countableDiaryLeafPrefix H (m + 1) =
          ({a,m} : Finset Nat) := by
      rw [countableDiaryLeafPrefix_succ_of_leaf H m hm,hOld]
      ext u
      simp only [Finset.mem_insert,Finset.mem_singleton]
      tauto
    have hSupport :
        countableDiaryFiniteSupport H (m + 1) =
          finiteLeafMeetSupport H ({a,m} : Finset Nat) := by
      change finiteLeafMeetSupport H
        (countableDiaryLeafPrefix H (m + 1)) =
          finiteLeafMeetSupport H ({a,m} : Finset Nat)
      rw [hNewPrefix]
    have hReserve : FutureOrderReserve H (m + 1) g := by
      apply (DH.second_leaf_reserve_iff_three_gaps
        ha hm ham hOld g r w v hMark hGS hGA hGM).2
      exact ⟨hGap1,hGap2,hGap3⟩
    have hOrdered : ∀ u z : Nat,
        u ∈ finiteLeafMeetSupport H ({a,m} : Finset Nat) →
        z ∈ finiteLeafMeetSupport H ({a,m} : Finset Nat) →
        u < z → g u < g z := by
      intro u z hu hz huz
      have hNum := hReserve u z
        (by rw [hSupport]; exact hu)
        (by rw [hSupport]; exact hz) huz
      omega
    have hSelectedLeaves : ∀ u : Nat,
        u ∈ ({a,m} : Finset Nat) → IsLeaf H u := by
      intro u hu
      simp only [Finset.mem_insert,Finset.mem_singleton] at hu
      rcases hu with hUA | hUM
      · subst u
        exact ha
      · subst u
        exact hm
    have hSupportedLeaf : ∀ u : Nat,
        u ∈ countableDiaryFiniteSupport H (m + 1) →
        IsLeaf H u → u = a ∨ u = m := by
      intro u hu hLeaf
      have huSupport :
          u ∈ finiteLeafMeetSupport H ({a,m} : Finset Nat) := by
        rw [←hSupport]
        exact hu
      have huSelected :=
        finiteLeafMeetSupport_leaf_mem_L DH
          hSelectedLeaves huSupport hLeaf
      simpa only [Finset.mem_insert,Finset.mem_singleton] using huSelected
    have hOrderedLeafPair : ∀ u z : Nat,
        u ∈ countableDiaryFiniteSupport H (m + 1) →
        z ∈ countableDiaryFiniteSupport H (m + 1) →
        IsLeaf H u → IsLeaf H z →
        u < z → u = a ∧ z = m := by
      intro u z hu hz hU hZ huz
      rcases hSupportedLeaf u hu hU with hUA | hUM <;>
      rcases hSupportedLeaf z hz hZ with hZA | hZM <;> omega
    have hSix :
        countableDiaryFiniteSupport H (m + 1) =
          (Finset.range 3 ∪ ({a,m,s} : Finset Nat)) :=
      DH.second_leaf_support_eq_six ha hm ham hOld
    have hIncidence :=
      twoLeaf_induced_edge_iff_right_bit
        DH DK a m w v ha hm ham hwLeaf hvLeaf hWltV
        g hMark hGS hGA hGM hOrdered hBit
    let Q : AdmissibleCofinalDiaryStage H K F (m + 1) g := {
      ordered := by
        intro u z hu hz huz
        exact hOrdered u z
          (by rw [←hSupport]; exact hu)
          (by rw [←hSupport]; exact hz) huz
      marker_zero := hMark 0 (by omega)
      marker_one := hMark 1 (by omega)
      marker_two := hMark 2 (by omega)
      leaf_role := by
        intro u hu hLeaf
        rcases hSupportedLeaf u hu hLeaf with hUA | hUM
        · subst u
          rw [hGA]
          exact hwLeaf
        · subst u
          rw [hGM]
          exact hvLeaf
      one_split_role := by
        intro u hu hOne
        have huCase :
            u < 3 ∨ u = a ∨ u = m ∨ u = s := by
          rw [hSix] at hu
          simpa only [Finset.mem_union,Finset.mem_range,
            Finset.mem_insert,Finset.mem_singleton] using hu
        rcases huCase with hSmall | hUA | hUM | hUS
        · have hu3 := hOne.1
          omega
        · subst u
          exact False.elim (ha.2.1 hOne.2.1)
        · subst u
          exact False.elim (hm.2.1 hOne.2.1)
        · subst u
          rw [hGS]
          exact hrRole
      two_split_role := by
        intro u hu hTwo
        have hu' : u ∈ finiteLeafMeetSupport H
            ({a,m} : Finset Nat) := by
          rw [←hSupport]
          exact hu
        exact False.elim
          ((DH.no_twoSplit_in_twoLeafMeetSupport
              a m ha hm ham u hu') hTwo)
      induced_edge := by
        intro x y z hx hy hz hxy hyz
        exact hIncidence x y z
          (by rw [←hSupport]; exact hx)
          (by rw [←hSupport]; exact hy)
          (by rw [←hSupport]; exact hz) hxy hyz
      leaf_oneMeet := by
        intro u z hu hz hU hZ
        have huCases := hSupportedLeaf u hu hU
        have hzCases := hSupportedLeaf z hz hZ
        rcases huCases with hUA | hUM
        · rcases hzCases with hZA | hZM
          · subst u
            subst z
            simp only [Ordered3Graph.oneMeetLevel_self]
          · subst u
            subst z
            change K.oneMeetLevel (g a) (g m) = g s
            rw [hGA,hGM,hGS]
            rfl
        · rcases hzCases with hZA | hZM
          · subst u
            subst z
            calc
              K.oneMeetLevel (g m) (g a) =
                  K.oneMeetLevel (g a) (g m) :=
                    oneMeetLevel_comm K (g m) (g a)
              _ = g (H.oneMeetLevel a m) := by
                rw [hGA,hGM,hGS]
              _ = g (H.oneMeetLevel m a) := by
                rw [oneMeetLevel_comm H m a]
          · subst u
            subst z
            simp only [Ordered3Graph.oneMeetLevel_self]
      leaf_twoMeet := by
        intro u z p q hu hz hp hq huz hpq hU hZ hP hQ
        obtain ⟨hUA,hZM⟩ :=
          hOrderedLeafPair u z hu hz hU hZ huz
        obtain ⟨hPA,hQM⟩ :=
          hOrderedLeafPair p q hp hq hP hQ hpq
        subst u
        subst z
        subst p
        subst q
        rw [twoMeetLevel_self_pair H a m,
          twoMeetLevel_self_pair K (g a) (g m)]
      leaf_range := by
        intro u hu hLeaf
        rcases hSupportedLeaf u hu hLeaf with hUA | hUM
        · subst u
          obtain ⟨t,ht⟩ := P.1.leaf_range a haOldSup ha
          exact ⟨t,hGA.trans ht⟩
        · subst u
          obtain ⟨t,ht⟩ := hvRange
          exact ⟨t,hGM.trans ht⟩
    }
    refine ⟨g,⟨Q,hReserve⟩,?_,hGM⟩
    intro u hu
    have hUA : u = a := by
      rw [hOld] at hu
      simpa only [Finset.mem_singleton] using hu
    subst u
    exact hGA

end DiaryLeafPriority
end ThreeUniformDiaries
