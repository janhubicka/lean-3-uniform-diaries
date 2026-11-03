import ThreeUniformDiaries.DiaryFutureReserveFusion
import ThreeUniformDiaries.DiaryOneNewLeafSupportSuccessor

/-!
# Quantitative singleton-meet constraints at every new leaf step

The future-order reserve condition controls more than the numerical
distance between old leaf images and a fresh image v. For ANY old
selected leaf a<m, S1 creates a source singleton meet s=a meet m,
which is a genuine one-split strictly before a.

In an actual reserved successor, the corresponding target one-meet
t = (f a) meet v must fit THREE successive source intervals:

  2 < s < a < m,
  2 < t < f(a) < v,

and the order reserve strengthens this to

  s <= t,
  t+(a-s) <= f(a),
  f(a)+(m-a) <= v.

These explicit finite inequalities are NECESSARY even when the
target right-marker orientation bit is correct. No theorem here
constructs a target leaf satisfying them. This obstruction is
already implicit in the verified finite-table/reserve criterion;
the point is to expose it in a small, directly testable form.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A single new source leaf together with any old selected leaf
forces a numerical three-gap condition on its target one-meet in
every genuinely reserved relative successor. -/
theorem reserved_successor_old_leaf_new_meet_three_gaps
    {H K : Ordered3Graph Nat}
    {F f g : Nat → Nat} {m a : Nat}
    (DH : RoleDiary H)
    (hm : IsLeaf H m)
    (haOld : a ∈ countableDiaryLeafPrefix H m)
    (Q : ReservedDiaryStage H K F (m + 1) g)
    (hKeep : ∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
      g u = f u) :
    let s := H.oneMeetLevel a m
    let t := K.oneMeetLevel (f a) (g m)
    s ≤ t ∧ t + (a - s) ≤ f a ∧ f a + (m - a) ≤ g m := by
  obtain ⟨ha3,ham,haLeaf⟩ :=
    (mem_countableDiaryLeafPrefix_iff H m a).mp haOld
  let s := H.oneMeetLevel a m
  let t := K.oneMeetLevel (f a) (g m)
  have hOne : IsOneSplit H s :=
    DH.singleton_meets a m haLeaf hm (ne_of_lt ham)
  have hS3 : 3 ≤ s := hOne.1
  have hSLe : s ≤ a :=
    (H.oneMeetLevel_le_min a m).trans (min_le_left _ _)
  have hSNe : s ≠ a := by
    intro heq
    have haOne : IsOneSplit H a := by
      simpa only [heq] using hOne
    exact haLeaf.2.1 haOne.2.1
  have hSA : s < a := by omega
  let L := countableDiaryLeafPrefix H (m + 1)
  have haL : a ∈ L :=
    (countableDiaryLeafPrefix_mono H m (m + 1) (by omega)) haOld
  have hmL : m ∈ L :=
    (mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
      ⟨hm.1,by omega,hm⟩
  have haSupport :
      a ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_leaf H L a haL
  have hmSupport :
      m ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_leaf H L m hmL
  have hsSupport :
      s ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_oneMeet H L a m haL hmL (ne_of_lt ham)
  have h2Support :
      2 ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_marker H L 2 (by omega)
  have hOldImage : g a = f a := hKeep a haOld
  have hMeet : t = g s := by
    simpa only [t,s,hOldImage] using
      Q.1.leaf_oneMeet a m haSupport hmSupport haLeaf hm
  have h2Image : g 2 = 2 := Q.1.marker_two
  have hFirst := Q.2 2 s h2Support hsSupport (by omega)
  have hMiddle := Q.2 s a hsSupport haSupport hSA
  have hLast := Q.2 a m haSupport hmSupport ham
  dsimp
  constructor
  · omega
  constructor
  · omega
  · omega

/-- If the proposed target leaf v cannot fit the forced
one-split meet of an existing leaf a with the new leaf m,
then NO relative successor with v and future reserve exists.
This negative certificate does not assume target genericity. -/
theorem no_reserved_successor_of_new_pair_gap_failure
    {H K : Ordered3Graph Nat} {F f : Nat → Nat}
    {m a v : Nat}
    (DH : RoleDiary H) (hm : IsLeaf H m)
    (haOld : a ∈ countableDiaryLeafPrefix H m)
    (hBad :
      let s := H.oneMeetLevel a m
      let t := K.oneMeetLevel (f a) v
      ¬ (s ≤ t ∧ t + (a - s) ≤ f a ∧
         f a + (m - a) ≤ v)) :
    ¬ ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1) g ∧
      (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
        g u = f u) ∧
      g m = v := by
  rintro ⟨g,Q,hKeep,hNew⟩
  have hGaps :=
    reserved_successor_old_leaf_new_meet_three_gaps
      DH hm haOld Q hKeep
  rw [hNew] at hGaps
  exact hBad hGaps

end DiaryLeafPriority
end ThreeUniformDiaries
