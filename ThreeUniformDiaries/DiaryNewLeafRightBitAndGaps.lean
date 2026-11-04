import ThreeUniformDiaries.DiaryNewLeafOneMeetGapBounds
import ThreeUniformDiaries.DiaryTwoLeafMarkerOrientation

/-!
# Every reserved new-leaf successor satisfies an old-new orientation bit

At any genuinely new source leaf m, every previously selected
source leaf a<m gives an actual source S1 one-split s=a meet m.
For a proposed relative successor preserving the old leaf image
f(a), its target singleton meet is forced to be

    t = K.oneMeetLevel(f(a),g(m)) = g(s).

The complete induced triple table in the new support therefore
requires the exact mixed right-marker bit

    E_H(0,s,m) iff E_K(0,t,g(m)),

in addition to the already proved three quantitative gap bounds.
Unlike the generic leaf-reduct incidence tests, the right-marker
bit involves a newly generated split.

Together with the verified two-leaf one-bit theorem, this identifies
ONE orientation requirement for every old-new selected leaf pair.
It is a NECESSARY finite certificate, never a construction of v.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Any admissible reserved successor preserves the right E2
orientation between each old selected leaf and the new source leaf,
and respects three adjacent future-order gaps around their meet. -/
theorem reserved_successor_old_new_right_bit_and_three_gaps
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
    (H.edge 0 s m ↔ K.edge 0 t (g m)) ∧
      s ≤ t ∧ t + (a - s) ≤ f a ∧
      f a + (m - a) ≤ g m := by
  obtain ⟨ha3,ham,haLeaf⟩ :=
    (mem_countableDiaryLeafPrefix_iff H m a).mp haOld
  let s := H.oneMeetLevel a m
  let t := K.oneMeetLevel (f a) (g m)
  have hsRole : IsOneSplit H s :=
    DH.singleton_meets a m haLeaf hm (ne_of_lt ham)
  have hs3 : 3 ≤ s := hsRole.1
  have hsLeA : s ≤ a :=
    (H.oneMeetLevel_le_min a m).trans (min_le_left _ _)
  let L := countableDiaryLeafPrefix H (m + 1)
  have haL : a ∈ L :=
    (countableDiaryLeafPrefix_mono H m (m + 1) (by omega)) haOld
  have hmL : m ∈ L :=
    (mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
      ⟨hm.1,by omega,hm⟩
  have h0Support :
      0 ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_marker H L 0 (by omega)
  have haSupport :
      a ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_leaf H L a haL
  have hmSupport :
      m ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_leaf H L m hmL
  have hsSupport :
      s ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_oneMeet H L
      a m haL hmL (ne_of_lt ham)
  have hMeet : t = g s := by
    have hOld : g a = f a := hKeep a haOld
    simpa only [t,s,hOld] using
      Q.1.leaf_oneMeet a m haSupport hmSupport haLeaf hm
  have hEdge :
      H.edge 0 s m ↔ K.edge 0 t (g m) := by
    have h := Q.1.induced_edge 0 s m
      h0Support hsSupport hmSupport (by omega) (by omega)
    rw [Q.1.marker_zero, ← hMeet] at h
    exact h
  have hGaps :=
    reserved_successor_old_leaf_new_meet_three_gaps
      DH hm haOld Q hKeep
  dsimp
  exact ⟨hEdge,hGaps⟩

/-- A proposed new target value v with either the wrong right
split/leaf bit or any of the three forced gaps missing cannot
be a reserved successor while keeping the older selected leaves.
This certificate does not assert existence of any good v. -/
theorem no_reserved_successor_of_bad_old_new_pair_profile
    {H K : Ordered3Graph Nat} {F f : Nat → Nat}
    {m a v : Nat}
    (DH : RoleDiary H)
    (hm : IsLeaf H m)
    (haOld : a ∈ countableDiaryLeafPrefix H m)
    (hBad :
      let s := H.oneMeetLevel a m
      let t := K.oneMeetLevel (f a) v
      ¬ ((H.edge 0 s m ↔ K.edge 0 t v) ∧
         s ≤ t ∧ t + (a - s) ≤ f a ∧
         f a + (m - a) ≤ v)) :
    ¬ ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1) g ∧
      (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
        g u = f u) ∧ g m = v := by
  rintro ⟨g,Q,hKeep,hNew⟩
  have hRequired :=
    reserved_successor_old_new_right_bit_and_three_gaps
      DH hm haOld Q hKeep
  rw [hNew] at hRequired
  exact hBad hRequired

end DiaryLeafPriority
end ThreeUniformDiaries
