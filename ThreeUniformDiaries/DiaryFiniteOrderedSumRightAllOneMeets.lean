import ThreeUniformDiaries.DiaryFiniteOrderedSumRightAllSingletonTypes
import ThreeUniformDiaries.DiaryFiniteOrderedSumRightExactMeets

/-!
# Exact singleton meets on all translated right nonmarker vertices

The right singleton type transport is now proved for arbitrary
right vertex roles, including split/split and leaf/split. We apply
this equivalence to the greatest capped agreement cut.

At marker meets 0,1,2 the original marker tests are copied exactly.
At source meet s>=3 the translated cut f(s) is exact; if the meet
is capped at a source endpoint, its image is also the target cap.
Otherwise s+1 is the first disagreement, and f(s+1)=f(s)+1.

Thus the entire right copy preserves singleton meet NUMBERS for
all pairs of nonmarker vertices, without source S1/S2. Together
with the independent exact auxiliary-meet theorem this prepares
the full protected ordered-pair result.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- Exact numerical preservation of every marker-capped right
singleton meet, including mixed source roles. -/
theorem finiteTwoBlockCarrier_right_oneMeet_small_all
    (FH : FiniteDiaryEdgeFrame H n)
    (PK : FiniteRolePrediaryBlock K m)
    (bits : Nat → Bool)
    (u v : Nat) (hu3 : 3 ≤ u) (hv3 : 3 ≤ v)
    (hs : K.oneMeetLevel u v < 3) :
    (finiteTwoBlockCarrier H K n m bits).oneMeetLevel
        (rightBlockImage n u) (rightBlockImage n v) =
      K.oneMeetLevel u v := by
  classical
  let G := finiteTwoBlockCarrier H K n m bits
  let s := K.oneMeetLevel u v
  have hSourceAt : K.SameOneTypeBelow s u v :=
    K.oneMeetLevel_agree u v
  have hSourceNextFail : ¬ K.SameOneTypeBelow (s + 1) u v := by
    intro ht
    have hCap : s + 1 ≤ min u v := by
      have hCap0 := K.oneMeetLevel_le_min u v
      dsimp [s] at *
      omega
    have hTooLarge : s + 1 ≤ K.oneMeetLevel u v :=
      Nat.le_findGreatest hCap ht
    dsimp [s] at *
    omega
  have hTargetAt :
      G.SameOneTypeBelow s
        (rightBlockImage n u) (rightBlockImage n v) :=
    (finiteTwoBlockCarrier_right_oneType_marker_iff
      FH PK.frame bits s u v (by omega)).mpr hSourceAt
  have hTargetNextFail :
      ¬ G.SameOneTypeBelow (s + 1)
          (rightBlockImage n u) (rightBlockImage n v) := by
    intro ht
    exact hSourceNextFail
      ((finiteTwoBlockCarrier_right_oneType_marker_iff
        FH PK.frame bits (s+1) u v (by omega)).mp ht)
  have huBound := rightBlockImage_nonmarker_ge
    n u FH.length_ge_three hu3
  have hvBound := rightBlockImage_nonmarker_ge
    n v FH.length_ge_three hv3
  have hCapTarget : s ≤ min (rightBlockImage n u)
      (rightBlockImage n v) := by
    have hn3 := FH.length_ge_three
    omega
  have hLower : s ≤ G.oneMeetLevel
      (rightBlockImage n u) (rightBlockImage n v) :=
    Nat.le_findGreatest hCapTarget hTargetAt
  have hUpper : G.oneMeetLevel
      (rightBlockImage n u) (rightBlockImage n v) < s + 1 := by
    by_contra hbad
    have hGe : s + 1 ≤ G.oneMeetLevel
        (rightBlockImage n u) (rightBlockImage n v) := by omega
    have hAgree := G.oneMeetLevel_agree
      (rightBlockImage n u) (rightBlockImage n v)
    apply hTargetNextFail
    intro a b hab hb
    exact hAgree hab (by omega)
  change G.oneMeetLevel
      (rightBlockImage n u) (rightBlockImage n v) = s
  omega

/-- At any original right meet s>=3, the exact source meet is
carried to translated cut f(s), both for proper and capped
singleton comparisons. No source S1/S2 is needed. -/
theorem finiteTwoBlockCarrier_right_oneMeet_large_all
    (FH : FiniteDiaryEdgeFrame H n)
    (PK : FiniteRolePrediaryBlock K m)
    (hEH : ∀ x y z : Nat, H.edge x y z →
      PermittedDiaryEdge H x y z)
    (bits : Nat → Bool)
    (u v : Nat) (hu3 : 3 ≤ u) (hum : u < m)
    (hv3 : 3 ≤ v) (hvm : v < m)
    (hs : 3 ≤ K.oneMeetLevel u v) :
    (finiteTwoBlockCarrier H K n m bits).oneMeetLevel
        (rightBlockImage n u) (rightBlockImage n v) =
      rightBlockImage n (K.oneMeetLevel u v) := by
  classical
  let G := finiteTwoBlockCarrier H K n m bits
  let s := K.oneMeetLevel u v
  have hs3 : 3 ≤ s := hs
  have hsCap : s ≤ min u v := K.oneMeetLevel_le_min u v
  have hsu : s ≤ u := hsCap.trans (min_le_left _ _)
  have hsv : s ≤ v := hsCap.trans (min_le_right _ _)
  have hMon := rightBlockImage_strictMono n FH.length_ge_three
  have hTargetAt : G.SameOneTypeBelow (rightBlockImage n s)
      (rightBlockImage n u) (rightBlockImage n v) :=
    (finiteTwoBlockCarrier_right_oneType_general_iff
      FH PK hEH bits s u v hs3 hu3 hum hv3 hvm).mpr
        (K.oneMeetLevel_agree u v)
  have hCapTarget : rightBlockImage n s ≤
      min (rightBlockImage n u) (rightBlockImage n v) := by
    have huMon := hMon.monotone hsu
    have hvMon := hMon.monotone hsv
    omega
  have hLower : rightBlockImage n s ≤
      G.oneMeetLevel (rightBlockImage n u) (rightBlockImage n v) :=
    Nat.le_findGreatest hCapTarget hTargetAt
  by_cases hCapped : s = min u v
  · have hMinImage : min (rightBlockImage n u)
        (rightBlockImage n v) = rightBlockImage n s := by
      rcases le_total u v with huv | hvu
      · have hsEq : s = u := by
          simpa only [min_eq_left huv] using hCapped
        rw [min_eq_left (hMon.monotone huv), hsEq]
      · have hsEq : s = v := by
          simpa only [min_eq_right hvu] using hCapped
        rw [min_eq_right (hMon.monotone hvu), hsEq]
    have hUpper := G.oneMeetLevel_le_min
      (rightBlockImage n u) (rightBlockImage n v)
    change G.oneMeetLevel (rightBlockImage n u)
      (rightBlockImage n v) = rightBlockImage n s
    omega
  · have hStrict : s < min u v := by omega
    have hSourceNextFail : ¬ K.SameOneTypeBelow (s+1) u v := by
      intro ht
      have hCap : s+1 ≤ min u v := by omega
      have hTooLarge : s+1 ≤ K.oneMeetLevel u v :=
        Nat.le_findGreatest hCap ht
      dsimp [s] at *
      omega
    have hTargetNextFail :
        ¬ G.SameOneTypeBelow (rightBlockImage n s + 1)
          (rightBlockImage n u) (rightBlockImage n v) := by
      intro ht
      have hNext : G.SameOneTypeBelow (rightBlockImage n (s+1))
          (rightBlockImage n u) (rightBlockImage n v) := by
        rwa [rightBlockImage_succ_of_ge_three n s hs3]
      exact hSourceNextFail
        ((finiteTwoBlockCarrier_right_oneType_general_iff
          FH PK hEH bits (s+1) u v (by omega)
          hu3 hum hv3 hvm).mp hNext)
    have hUpper : G.oneMeetLevel
        (rightBlockImage n u) (rightBlockImage n v) <
          rightBlockImage n s + 1 := by
      by_contra hbad
      have hGe : rightBlockImage n s + 1 ≤ G.oneMeetLevel
          (rightBlockImage n u) (rightBlockImage n v) := by omega
      have hAgree := G.oneMeetLevel_agree
        (rightBlockImage n u) (rightBlockImage n v)
      apply hTargetNextFail
      intro a b hab hb
      exact hAgree hab (by omega)
    change G.oneMeetLevel (rightBlockImage n u)
      (rightBlockImage n v) = rightBlockImage n s
    omega

/-- Exactly preserves EVERY capped singleton meet of any two
right vertices within the bounded source block: diagonal,
leaf/leaf, split/split, and both mixed orientations. -/
theorem finiteTwoBlockCarrier_right_oneMeet_exact_all
    (FH : FiniteDiaryEdgeFrame H n)
    (PK : FiniteRolePrediaryBlock K m)
    (hEH : ∀ x y z : Nat, H.edge x y z →
      PermittedDiaryEdge H x y z)
    (bits : Nat → Bool)
    (u v : Nat)
    (hu3 : 3 ≤ u) (hum : u < m)
    (hv3 : 3 ≤ v) (hvm : v < m) :
    (finiteTwoBlockCarrier H K n m bits).oneMeetLevel
        (rightBlockImage n u) (rightBlockImage n v) =
      rightBlockImage n (K.oneMeetLevel u v) := by
  by_cases hs : K.oneMeetLevel u v < 3
  · have hSmall := finiteTwoBlockCarrier_right_oneMeet_small_all
      FH PK bits u v hu3 hv3 hs
    have hFix := rightBlockImage_marker n
      (K.oneMeetLevel u v) hs
    rw [hFix]
    exact hSmall
  · exact finiteTwoBlockCarrier_right_oneMeet_large_all
      FH PK hEH bits u v hu3 hum hv3 hvm (by omega)

end DiaryLeafPriority
end ThreeUniformDiaries
