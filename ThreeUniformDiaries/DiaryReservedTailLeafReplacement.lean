import ThreeUniformDiaries.DiaryTailFullPairMeetCone
import ThreeUniformDiaries.DiaryNewLeafMaxSupport
import ThreeUniformDiaries.DiaryFutureReserveFusion
import ThreeUniformDiaries.DiaryTwoLeafExactSixSupport

/-!
# A genuine reserved new-leaf stage is closed under old-cut type tails

Suppose an actual ReservedDiaryStage at a genuine newly selected
source leaf m sends m to v0. Fix a cut B larger than the images
of every other vertex in S_(m+1). If v is a later genuine target
leaf in the prescribed F-range, with the SAME complete singleton
type as v0 below B, then replacing ONLY the image of m by v
produces another reserved stage.

The proof checks every field:
  strict order and FUTURE numerical reserve,
  all actual source roles and marker images,
  all induced triples AND nontriples,
  exact source-leaf singleton meets,
  exact full ordered-leaf-pair meets,
  the prescribed range of every selected leaf.

The key point is that m is the LARGEST source coordinate of
its generated successor support. Every old or new nonleaf
generator keeps its image. All mixed edge tests and numeric
meet comparisons of the new leaf are decided strictly below B.

This is a positive relative TAIL-REPLACEMENT theorem for an
ALREADY AVAILABLE new leaf. It does not say that the prescribed
unordered leaf copy contains another element of that mixed
type cone; nor does one-step replacement establish persistence
through arbitrary further horizons.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Replace the image of a single source vertex, fixing every other
coordinate of the total map. -/
def replaceAt (g0 : Nat → Nat) (m v : Nat) (u : Nat) : Nat :=
  if u = m then v else g0 u

theorem replaceAt_eq (g0 : Nat → Nat) (m v : Nat) :
    replaceAt g0 m v m = v := by simp [replaceAt]

theorem replaceAt_other (g0 : Nat → Nat) (m v u : Nat)
    (hu : u ≠ m) :
    replaceAt g0 m v u = g0 u := by simp [replaceAt,hu]

/-- Exact one-step replacement of a genuine new leaf in the SAME
mixed singleton-type cone over all old source support images.

B need only dominate the FINITELY MANY images of supported source
coordinates other than m. It is not an additional genericity
assumption and such a cut always exists for any supplied stage. -/
theorem ReservedDiaryStage.replace_new_leaf_of_same_tail_type
    {H K : Ordered3Graph Nat} {F g0 : Nat → Nat}
    {m B v : Nat}
    (hm : IsLeaf H m)
    (P : ReservedDiaryStage H K F (m + 1) g0)
    (hBelow : ∀ u : Nat,
      u ∈ countableDiaryFiniteSupport H (m + 1) →
      u ≠ m → g0 u < B)
    (hTail : K.SameOneTypeBelow B (g0 m) v)
    (hvLater : g0 m ≤ v)
    (hvLeaf : IsLeaf K v)
    (hvRange : ∃ t : Nat, v = F t) :
    ReservedDiaryStage H K F (m + 1)
      (replaceAt g0 m v) := by
  classical
  let S := countableDiaryFiniteSupport H (m + 1)
  let g := replaceAt g0 m v
  have hmS : m ∈ S := by
    apply mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H (m + 1)) m
    exact (mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
      ⟨hm.1,by omega,hm⟩
  have hMax (u : Nat) (hu : u ∈ S) : u ≤ m :=
    countableDiaryFiniteSupport_succ_le_new_leaf H m u hm hu
  have hOther (u : Nat) (hu : u ≠ m) :
      replaceAt g0 m v u = g0 u :=
    replaceAt_other g0 m v u hu
  have hNew : replaceAt g0 m v m = v := replaceAt_eq g0 m v
  have hOldLt (u : Nat) (hu : u ∈ S) (hum : u < m) :
      g0 u < g0 m :=
    P.1.ordered u m hu hmS hum
  have hOldMeet (u : Nat) (hu : u ∈ S) (hum : u < m) :
      K.oneMeetLevel (g0 u) v =
        K.oneMeetLevel (g0 u) (g0 m) := by
    exact (oneMeetLevel_eq_of_sameOneTypeBelow_cut
      K B (g0 u) (g0 m) v
      (hBelow u hu (ne_of_lt hum))
      (hOldLt u hu hum)
      (lt_of_lt_of_le (hOldLt u hu hum) hvLater)
      hTail).symm
  have hNewAfterOld (u : Nat) (hu : u ∈ S) (hum : u < m) :
      K.oneMeetLevel (g u) (g m) =
        K.oneMeetLevel (g0 u) (g0 m) := by
    rw [hOther u (ne_of_lt hum),hNew]
    exact hOldMeet u hu hum
  refine ⟨?_,?_⟩
  · refine {
      ordered := ?_
      marker_zero := ?_
      marker_one := ?_
      marker_two := ?_
      leaf_role := ?_
      one_split_role := ?_
      two_split_role := ?_
      induced_edge := ?_
      leaf_oneMeet := ?_
      leaf_twoMeet := ?_
      leaf_range := ?_
    }
    · intro u w hu hw huw
      have hwMax := hMax w hw
      have huNe : u ≠ m := by omega
      by_cases hwEq : w = m
      · subst w
        rw [hOther u huNe,hNew]
        exact lt_of_lt_of_le (P.1.ordered u m hu hmS huw) hvLater
      · rw [hOther u huNe,hOther w hwEq]
        exact P.1.ordered u w hu hw huw
    · rw [hOther 0 (by have hm3 := hm.1; omega)]
      exact P.1.marker_zero
    · rw [hOther 1 (by have hm3 := hm.1; omega)]
      exact P.1.marker_one
    · rw [hOther 2 (by have hm3 := hm.1; omega)]
      exact P.1.marker_two
    · intro u hu hLeaf
      by_cases huM : u = m
      · subst u
        rw [hNew]
        exact hvLeaf
      · rw [hOther u huM]
        exact P.1.leaf_role u hu hLeaf
    · intro u hu hOne
      have huNe : u ≠ m := by
        intro hEq
        subst u
        exact hm.2.1 hOne.2.1
      rw [hOther u huNe]
      exact P.1.one_split_role u hu hOne
    · intro u hu hTwo
      have huNe : u ≠ m := by
        intro hEq
        subst u
        exact hm.2.2 hTwo.2.2
      rw [hOther u huNe]
      exact P.1.two_split_role u hu hTwo
    · intro x y z hx hy hz hxy hyz
      have hzMax : z ≤ m := hMax z hz
      have hxNe : x ≠ m := by omega
      have hyNe : y ≠ m := by omega
      by_cases hzM : z = m
      · subst z
        rw [hOther x hxNe,hOther y hyNe,hNew]
        have hXY : g0 x < g0 y :=
          P.1.ordered x y hx hy hxy
        have hyB : g0 y < B := hBelow y hy hyNe
        exact (P.1.induced_edge x y m hx hy hz hxy hyz).trans
          (hTail hXY hyB)
      · rw [hOther x hxNe,hOther y hyNe,hOther z hzM]
        exact P.1.induced_edge x y z hx hy hz hxy hyz
    · intro a b ha hb hLa hLb
      have haMax := hMax a ha
      have hbMax := hMax b hb
      by_cases haM : a = m
      · subst a
        by_cases hbM : b = m
        · subst b
          simp only [Ordered3Graph.oneMeetLevel_self]
        · have hbLt : b < m := by omega
          have hMeetLt : H.oneMeetLevel m b < m := by
            have hBound := (H.oneMeetLevel_le_min m b).trans
              (min_le_right _ _)
            omega
          calc
            K.oneMeetLevel (g m) (g b) =
                K.oneMeetLevel (g b) (g m) :=
                  oneMeetLevel_comm K (g m) (g b)
            _ = K.oneMeetLevel (g0 b) (g0 m) :=
                  hNewAfterOld b hb hbLt
            _ = K.oneMeetLevel (g0 m) (g0 b) :=
                  oneMeetLevel_comm K (g0 b) (g0 m)
            _ = g0 (H.oneMeetLevel m b) :=
                  P.1.leaf_oneMeet m b ha hb hLa hLb
            _ = g (H.oneMeetLevel m b) :=
                  (hOther _ (by omega)).symm
      · by_cases hbM : b = m
        · subst b
          have haLt : a < m := by omega
          have hMeetLt : H.oneMeetLevel a m < m := by
            have hBound := (H.oneMeetLevel_le_min a m).trans
              (min_le_left _ _)
            omega
          calc
            K.oneMeetLevel (g a) (g m) =
                K.oneMeetLevel (g0 a) (g0 m) :=
                  hNewAfterOld a ha haLt
            _ = g0 (H.oneMeetLevel a m) :=
                  P.1.leaf_oneMeet a m ha hb hLa hLb
            _ = g (H.oneMeetLevel a m) :=
                  (hOther _ (by omega)).symm
        · have hMeetLt : H.oneMeetLevel a b < m := by
            have hBound := (H.oneMeetLevel_le_min a b).trans
              (min_le_left _ _)
            omega
          calc
            K.oneMeetLevel (g a) (g b) =
                K.oneMeetLevel (g0 a) (g0 b) := by
                  rw [hOther a haM,hOther b hbM]
            _ = g0 (H.oneMeetLevel a b) :=
                  P.1.leaf_oneMeet a b ha hb hLa hLb
            _ = g (H.oneMeetLevel a b) :=
                  (hOther _ (by omega)).symm
    · intro a b c d ha hb hc hd hab hcd hLa hLb hLc hLd
      have hbMax := hMax b hb
      have hdMax := hMax d hd
      have haLt : a < m := by omega
      have hcLt : c < m := by omega
      have haNe : a ≠ m := ne_of_lt haLt
      have hcNe : c ≠ m := ne_of_lt hcLt
      have hbTail : K.SameOneTypeBelow B (g0 b) (g b) := by
        by_cases hbM : b = m
        · subst b
          rw [hNew]
          exact hTail
        · rw [hOther b hbM]
          intro x y _ _
          exact Iff.rfl
      have hdTail : K.SameOneTypeBelow B (g0 d) (g d) := by
        by_cases hdM : d = m
        · subst d
          rw [hNew]
          exact hTail
        · rw [hOther d hdM]
          intro x y _ _
          exact Iff.rfl
      have hTwoEq :
          K.twoMeetLevel (g0 a) (g0 b) (g0 c) (g0 d) =
          K.twoMeetLevel (g0 a) (g b) (g0 c) (g d) :=
        twoMeetLevel_eq_of_second_tail_types
          K B (g0 a) (g0 c) (g0 b) (g b) (g0 d) (g d)
          (hBelow a ha haNe) (hBelow c hc hcNe)
          hbTail hdTail
      have hMeetLt : H.twoMeetLevel a b c d < m := by
        have hBound := (H.twoMeetLevel_le_min a b c d).trans
          (min_le_left _ _)
        omega
      calc
        K.twoMeetLevel (g a) (g b) (g c) (g d) =
            K.twoMeetLevel (g0 a) (g b) (g0 c) (g d) := by
              rw [hOther a haNe,hOther c hcNe]
        _ = K.twoMeetLevel (g0 a) (g0 b) (g0 c) (g0 d) :=
              hTwoEq.symm
        _ = g0 (H.twoMeetLevel a b c d) :=
              P.1.leaf_twoMeet a b c d
                ha hb hc hd hab hcd hLa hLb hLc hLd
        _ = g (H.twoMeetLevel a b c d) :=
              (hOther _ (by omega)).symm
    · intro u hu hLeaf
      by_cases huM : u = m
      · subst u
        rw [hNew]
        exact hvRange
      · rw [hOther u huM]
        exact P.1.leaf_range u hu hLeaf
  · intro x y hx hy hxy
    have hyMax := hMax y hy
    have hxNe : x ≠ m := by omega
    by_cases hyM : y = m
    · subst y
      rw [hOther x hxNe,hNew]
      exact (P.2 x m hx hmS hxy).trans hvLater
    · rw [hOther x hxNe,hOther y hyM]
      exact P.2 x y hx hy hxy

end DiaryLeafPriority
end ThreeUniformDiaries
