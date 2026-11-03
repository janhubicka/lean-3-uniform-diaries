import ThreeUniformDiaries.DiaryShiftedSeedExactAuxMeet

/-!
# Track B: exact full two-meet shift at a proper first singleton disagreement

For a<b whose first singleton meet r is proper (r<a), the actual
full two-type meet of the pairs (r,a),(r,b) in the three-marker seed is
exactly the original full meet shifted by three.

This theorem does NOT claim a shift for arbitrary capped full pair-meets.
It uses the already verified exact singleton and auxiliary-meet shifts
and the literal decomposition of full two-types into coordinate
singleton types and auxiliary type. The source's common singleton prefix
at r is provided by the genuine numerical first meet itself.

No diary axioms, Ramsey theorem or countable unavoidability are used.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

private theorem oneMeetLevel_self_for_shift
    (H : Ordered3Graph Nat) (t : Nat) :
    H.oneMeetLevel t t = t := by
  classical
  apply Nat.le_antisymm
  · simpa only [min_self] using H.oneMeetLevel_le_min t t
  · apply Nat.le_findGreatest (by simp)
    intro x y hxy hy
    rfl

/-- The actual deciding *full* pair-meet shifts by exactly three at a
proper first singleton disagreement. Both pairs must be genuinely
ordered; this is why the proper-meet hypothesis is essential. -/
theorem shiftedDiarySeed_twoMeetLevel_exact_of_properOneMeet
    (H : Ordered3Graph Nat) (a b : Nat)
    (hab : a < b) (hproper : H.oneMeetLevel a b < a) :
    let r := H.oneMeetLevel a b
    (shiftedDiarySeed H).twoMeetLevel
      (r+3) (a+3) (r+3) (b+3) =
      H.twoMeetLevel r a r b + 3 := by
  classical
  dsimp
  let r := H.oneMeetLevel a b
  have hra : r < a := hproper
  have hrb : r < b := by omega
  have hAB : H.SameOneTypeBelow r a b := H.oneMeetLevel_agree a b
  have hAux :
      (shiftedDiarySeed H).auxMeetLevel
        (r+3) (a+3) (r+3) (b+3) =
        H.auxMeetLevel r a r b + 3 :=
    shiftedDiarySeed_auxMeetLevel_exact H r a b hra hrb hAB
  have hOne :
      (shiftedDiarySeed H).oneMeetLevel (a+3) (b+3) = r+3 :=
    shiftedDiarySeed_oneMeetLevel_exact H a b hab
  have hSelfH := oneMeetLevel_self_for_shift H r
  have hSelfS := oneMeetLevel_self_for_shift (shiftedDiarySeed H) (r+3)
  have hAuxBound : H.auxMeetLevel r a r b ≤ r := by
    have h := H.auxMeetLevel_le_min r a r b
    omega
  have hSourceTwo :
      H.twoMeetLevel r a r b = H.auxMeetLevel r a r b := by
    calc
      H.twoMeetLevel r a r b =
          min (H.auxMeetLevel r a r b)
            (min (H.oneMeetLevel r r) (H.oneMeetLevel a b)) :=
        H.twoMeetLevel_eq_min r a r b hra hrb
      _ = min (H.auxMeetLevel r a r b) r := by
        rw [hSelfH]
        change min (H.auxMeetLevel r a r b) (min r r) =
          min (H.auxMeetLevel r a r b) r
        simp
      _ = H.auxMeetLevel r a r b := min_eq_left hAuxBound
  have hTargetTwo :
      (shiftedDiarySeed H).twoMeetLevel
          (r+3) (a+3) (r+3) (b+3) =
        H.auxMeetLevel r a r b + 3 := by
    calc
      (shiftedDiarySeed H).twoMeetLevel
          (r+3) (a+3) (r+3) (b+3) =
          min ((shiftedDiarySeed H).auxMeetLevel
            (r+3) (a+3) (r+3) (b+3))
            (min ((shiftedDiarySeed H).oneMeetLevel (r+3) (r+3))
              ((shiftedDiarySeed H).oneMeetLevel (a+3) (b+3))) :=
        (shiftedDiarySeed H).twoMeetLevel_eq_min
          (r+3) (a+3) (r+3) (b+3) (by omega) (by omega)
      _ = min (H.auxMeetLevel r a r b + 3) (r+3) := by
        rw [hAux, hSelfS, hOne]
        simp only [min_self]
      _ = H.auxMeetLevel r a r b + 3 :=
        min_eq_left (by omega)
  exact hTargetTwo.trans
    (congrArg (fun n : Nat => n + 3) hSourceTwo.symm)

end DiaryLeafPriority
end ThreeUniformDiaries
