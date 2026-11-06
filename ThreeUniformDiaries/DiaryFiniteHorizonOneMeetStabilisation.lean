import ThreeUniformDiaries.DiaryFiniteHorizonChoice
import ThreeUniformDiaries.DiaryNewLeafRightBitAndGaps

/-!
# The new leaf's one-meet with an OLD leaf can be stabilized

Fix the existing image w=f(a) of an earlier selected source leaf a.
Even if the new leaf image g(m) ranges over infinitely many values,
its singleton meet K.oneMeetLevel w (g m) is bounded by w, by the
capped definition. Thus there are finitely many possible meet LEVELS.

If the old supported images admit relative reserved extensions
through every finite horizon, finite-choice compactness fixes ONE
target singleton meet r that can recur at EVERY horizon. The new
leaf images may still move arbitrarily far out.

In a genuine source diary, the verified right-bit/three-gap
necessity shows that this stabilized split meets the correct
orientation requirement and first TWO quantitative gaps. Each
finite-horizon witness additionally meets the third distance bound.

No fixed next LEAF image or countable embedding is obtained. The
new positive conclusion is only persistence of a generator level.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A single old-new target meet LEVEL can be fixed through all
finite horizons because it lies below the already fixed old
target vertex f(a). No full diary axioms are needed here. -/
theorem old_new_oneMeet_stabilizes_over_finite_horizons
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m a : Nat}
    (hHorizons : ∀ n : Nat, ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1 + n) g ∧
      CofinalDiaryStageCompatible H m f g) :
    ∃ r : Nat, r ≤ f a ∧
      ∀ n : Nat, ∃ g : Nat → Nat,
        ReservedDiaryStage H K F (m + 1 + n) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        K.oneMeetLevel (f a) (g m) = r := by
  classical
  let W : Finset Nat := Finset.range (f a + 1)
  let P : Nat → Nat → Prop := fun r n =>
    ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1 + n) g ∧
      CofinalDiaryStageCompatible H m f g ∧
      K.oneMeetLevel (f a) (g m) = r
  have hDown : ∀ r n k : Nat, k ≤ n → P r n → P r k := by
    intro r n k hkn
    rintro ⟨g,Q,hOld,hR⟩
    exact ⟨g,Q.restrict (by omega),hOld,hR⟩
  have hFinite : ∀ n : Nat, ∃ r : Nat, r ∈ W ∧ P r n := by
    intro n
    obtain ⟨g,Q,hOld⟩ := hHorizons n
    let r := K.oneMeetLevel (f a) (g m)
    have hBound : r ≤ f a :=
      (K.oneMeetLevel_le_min (f a) (g m)).trans
        (min_le_left _ _)
    refine ⟨r,?_ ,g,Q,hOld,rfl⟩
    exact Finset.mem_range.mpr (by omega)
  obtain ⟨r,hr,hAll⟩ :=
    finite_choice_persistent_of_downward W P hDown hFinite
  refine ⟨r,?_,hAll⟩
  have hrSmall : r < f a + 1 := Finset.mem_range.mp hr
  omega

/-- Once a full source diary has an old selected leaf a and the
new position m is also a leaf, the stabilized meet r must satisfy
all source-specific S1 orientation and numeric-gap obligations.
The last gap is required separately of each (possibly moving)
next-leaf image. -/
theorem old_new_split_profile_stabilizes_over_finite_horizons
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m a : Nat}
    (DH : RoleDiary H)
    (hm : IsLeaf H m)
    (haOld : a ∈ countableDiaryLeafPrefix H m)
    (hHorizons : ∀ n : Nat, ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1 + n) g ∧
      CofinalDiaryStageCompatible H m f g) :
    ∃ r : Nat,
      H.oneMeetLevel a m ≤ r ∧
      r + (a - H.oneMeetLevel a m) ≤ f a ∧
      ∀ n : Nat, ∃ g : Nat → Nat,
        ReservedDiaryStage H K F (m + 1 + n) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        K.oneMeetLevel (f a) (g m) = r ∧
        (H.edge 0 (H.oneMeetLevel a m) m ↔
          K.edge 0 r (g m)) ∧
        f a + (m - a) ≤ g m := by
  obtain ⟨r,hrBound,hAll⟩ :=
    old_new_oneMeet_stabilizes_over_finite_horizons hHorizons
  have hNeeded (n : Nat) (g : Nat → Nat)
      (Qg : ReservedDiaryStage H K F (m + 1 + n) g)
      (hOld : CofinalDiaryStageCompatible H m f g) :
      (H.edge 0 (H.oneMeetLevel a m) m ↔
        K.edge 0 (K.oneMeetLevel (f a) (g m)) (g m)) ∧
      H.oneMeetLevel a m ≤ K.oneMeetLevel (f a) (g m) ∧
      K.oneMeetLevel (f a) (g m) +
          (a - H.oneMeetLevel a m) ≤ f a ∧
      f a + (m - a) ≤ g m := by
    have Qnext : ReservedDiaryStage H K F (m + 1) g :=
      Qg.restrict (by omega)
    have hKeep : ∀ u : Nat,
        u ∈ countableDiaryLeafPrefix H m → g u = f u := by
      intro u hu
      have huSupported : u ∈ countableDiaryFiniteSupport H m :=
        mem_finiteLeafMeetSupport_leaf H
          (countableDiaryLeafPrefix H m) u hu
      exact hOld u huSupported
    simpa only [] using
      reserved_successor_old_new_right_bit_and_three_gaps
        DH hm haOld Qnext hKeep
  obtain ⟨g0,Q0,hOld0,hMeet0⟩ := hAll 0
  have hReq0 := hNeeded 0 g0 Q0 hOld0
  rw [hMeet0] at hReq0
  refine ⟨r,hReq0.2.1,hReq0.2.2.1,?_⟩
  intro n
  obtain ⟨g,Q,hOld,hMeet⟩ := hAll n
  have hReq := hNeeded n g Q hOld
  rw [hMeet] at hReq
  exact ⟨g,Q,hOld,hMeet,hReq.1,hReq.2.2.2⟩

end DiaryLeafPriority
end ThreeUniformDiaries
