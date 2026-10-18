import ThreeUniformDiaries.DiaryFiniteOrderedSumRightAllOneMeets
import ThreeUniformDiaries.DiaryFiniteOrderedSumRightAuxExact
import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface

/-!
# Exact full ordered-pair meets in the translated right finite copy

The full two-type meet is the minimum of three NUMERIC meets:
singleton meets of the corresponding first coordinates,
singleton meets of the corresponding second coordinates, and
the auxiliary meet of the two ordered pairs.

The exact first- and second-coordinate right one-meets have
already been checked for every source role, including mixed
split/leaf comparisons, capped cases and diagonals. Independently,
the right auxiliary meet has been checked for arbitrary nonmarker
right pairs with no diary axioms at all.

The translation f = rightBlockImage is strictly increasing and
therefore preserves binary minimum. Combining those facts yields
exact full two-meet preservation for ANY two increasing ordered
pairs of vertices of the translated right finite block.

Only bounded source finite V/E and left E shapes are needed.
No original S1/S2, target V/E/S, or completion is assumed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- The actual monotone translation fixing markers commutes with
binary min, even though it inserts a nonmarker left block. -/
theorem rightBlockImage_min
    (n a b : Nat) (hn : 3 ≤ n) :
    rightBlockImage n (min a b) =
      min (rightBlockImage n a) (rightBlockImage n b) := by
  have hmono := (rightBlockImage_strictMono n hn).monotone
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, min_eq_left (hmono hab)]
  · rw [min_eq_right hba, min_eq_right (hmono hba)]

/-- Exact full two-meet preservation for any two ordered pairs of
right NONMARKER vertices, INCLUDING pairs with split endpoints,
capped first-leaf cases, and common coordinates. -/
theorem finiteTwoBlockCarrier_right_twoMeet_exact_all
    (FH : FiniteDiaryEdgeFrame H n)
    (PK : FiniteRolePrediaryBlock K m)
    (hEH : ∀ x y z : Nat, H.edge x y z →
      PermittedDiaryEdge H x y z)
    (bits : Nat → Bool)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha3 : 3 ≤ a) (ham : a < m)
    (hb3 : 3 ≤ b) (hbm : b < m)
    (hc3 : 3 ≤ c) (hcm : c < m)
    (hd3 : 3 ≤ d) (hdm : d < m) :
    (finiteTwoBlockCarrier H K n m bits).twoMeetLevel
        (rightBlockImage n a) (rightBlockImage n b)
        (rightBlockImage n c) (rightBlockImage n d) =
      rightBlockImage n (K.twoMeetLevel a b c d) := by
  let G := finiteTwoBlockCarrier H K n m bits
  have hMon := rightBlockImage_strictMono n FH.length_ge_three
  have hfAB := hMon hab
  have hfCD := hMon hcd
  have hFirst := finiteTwoBlockCarrier_right_oneMeet_exact_all
    FH PK hEH bits a c ha3 ham hc3 hcm
  have hSecond := finiteTwoBlockCarrier_right_oneMeet_exact_all
    FH PK hEH bits b d hb3 hbm hd3 hdm
  have hAux := finiteTwoBlockCarrier_right_auxMeet_exact
    FH PK.frame bits a b c d ha3 hb3 hc3 hd3
  change G.twoMeetLevel (rightBlockImage n a)
    (rightBlockImage n b) (rightBlockImage n c)
    (rightBlockImage n d) =
      rightBlockImage n (K.twoMeetLevel a b c d)
  rw [G.twoMeetLevel_eq_min
      (rightBlockImage n a) (rightBlockImage n b)
      (rightBlockImage n c) (rightBlockImage n d)
      hfAB hfCD,
    K.twoMeetLevel_eq_min a b c d hab hcd]
  rw [hFirst, hSecond, hAux]
  simp only [rightBlockImage_min n FH.length_ge_three]

end DiaryLeafPriority
end ThreeUniformDiaries
