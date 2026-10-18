import ThreeUniformDiaries.DiaryFiniteOrderedSumRightPairTransport
import ThreeUniformDiaries.DiaryFiniteOrderedSumRightExactMeets

/-!
# Exact auxiliary meets in the translated right finite block

The right copy is induced, and no new cross-copy edge can have a
nonmarker left vertex as its FIRST coordinate and both later
vertices in the right copy. Consequently all auxiliary tests
at left-block positions are zero. The only shifted nonzero tests
are copied genuine right-block tests.

We show numeric preservation of auxiliary meets for arbitrary
ordered pairs of right NONMARKER vertices. This includes mixed
pairs with split vertices, and capped meets, not just leaf pairs
with a proper first 2-split.

The proof first handles the three marker cuts directly by induced
right edge reflection. For source meets >=3, exact transport at
each translated right cut, with no gaps inside the right block,
gives either the strict successor disagreement or the capped case.

This module uses only finite increasing edge frames and does not
assume diary V/E/S axioms or any global countable completion.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- All right-copy auxiliary types at marker cuts through level 3
are reflected exactly, regardless of the orientation bits. -/
theorem finiteTwoBlockCarrier_right_auxType_marker_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (l a b c d : Nat) (hl : l ≤ 3) :
    ((finiteTwoBlockCarrier H K n m bits).SameAuxTypeBelow
       l (rightBlockImage n a) (rightBlockImage n b)
         (rightBlockImage n c) (rightBlockImage n d) ↔
      K.SameAuxTypeBelow l a b c d) := by
  constructor
  · intro ht x hx
    have hx3 : x < 3 := by omega
    have himage := rightBlockImage_marker n x hx3
    have heAB := finiteTwoBlockCarrier_right_edge_iff_all
      FH FK bits x a b
    have heCD := finiteTwoBlockCarrier_right_edge_iff_all
      FH FK bits x c d
    rw [himage] at heAB heCD
    exact heAB.symm.trans ((ht (a := x) hx).trans heCD)
  · intro hs x hx
    have hx3 : x < 3 := by omega
    have himage := rightBlockImage_marker n x hx3
    have heAB := finiteTwoBlockCarrier_right_edge_iff_all
      FH FK bits x a b
    have heCD := finiteTwoBlockCarrier_right_edge_iff_all
      FH FK bits x c d
    rw [himage] at heAB heCD
    exact heAB.trans ((hs (a := x) hx).trans heCD.symm)

/-- Any source auxiliary meet below the nonmarker cut 3 is
preserved NUMERICALLY. The first coordinates of the two right
pairs are genuine nonmarker vertices, so the target caps lie
after the unchanged marker cuts. -/
theorem finiteTwoBlockCarrier_right_auxMeet_small
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (a b c d : Nat) (ha3 : 3 ≤ a) (hc3 : 3 ≤ c)
    (hSmall : K.auxMeetLevel a b c d < 3) :
    (finiteTwoBlockCarrier H K n m bits).auxMeetLevel
        (rightBlockImage n a) (rightBlockImage n b)
        (rightBlockImage n c) (rightBlockImage n d) =
      K.auxMeetLevel a b c d := by
  classical
  let G := finiteTwoBlockCarrier H K n m bits
  let s := K.auxMeetLevel a b c d
  have hAt : K.SameAuxTypeBelow s a b c d :=
    K.auxMeetLevel_agree a b c d
  have hNextFail : ¬ K.SameAuxTypeBelow (s + 1) a b c d := by
    intro hs
    have hCap : s + 1 ≤ min a c := by
      have ha := K.auxMeetLevel_le_min a b c d
      dsimp [s] at *
      omega
    have hTooLarge : s + 1 ≤ K.auxMeetLevel a b c d :=
      Nat.le_findGreatest hCap hs
    dsimp [s] at *
    omega
  have hTargetAt :
      G.SameAuxTypeBelow s
        (rightBlockImage n a) (rightBlockImage n b)
        (rightBlockImage n c) (rightBlockImage n d) :=
    (finiteTwoBlockCarrier_right_auxType_marker_iff
      FH FK bits s a b c d (by omega)).mpr hAt
  have hTargetNextFail :
      ¬ G.SameAuxTypeBelow (s + 1)
        (rightBlockImage n a) (rightBlockImage n b)
        (rightBlockImage n c) (rightBlockImage n d) := by
    intro ht
    exact hNextFail
      ((finiteTwoBlockCarrier_right_auxType_marker_iff
        FH FK bits (s + 1) a b c d (by omega)).mp ht)
  have hAGe := rightBlockImage_nonmarker_ge n a
    FH.length_ge_three ha3
  have hCGe := rightBlockImage_nonmarker_ge n c
    FH.length_ge_three hc3
  have hCapTarget : s ≤ min (rightBlockImage n a)
      (rightBlockImage n c) := by
    have hn3 := FH.length_ge_three
    omega
  have hLower : s ≤ G.auxMeetLevel
      (rightBlockImage n a) (rightBlockImage n b)
      (rightBlockImage n c) (rightBlockImage n d) :=
    Nat.le_findGreatest hCapTarget hTargetAt
  have hUpper : G.auxMeetLevel
      (rightBlockImage n a) (rightBlockImage n b)
      (rightBlockImage n c) (rightBlockImage n d) < s + 1 := by
    by_contra hbad
    have hg : s + 1 ≤ G.auxMeetLevel
        (rightBlockImage n a) (rightBlockImage n b)
        (rightBlockImage n c) (rightBlockImage n d) := by omega
    have hAgree := G.auxMeetLevel_agree
      (rightBlockImage n a) (rightBlockImage n b)
      (rightBlockImage n c) (rightBlockImage n d)
    apply hTargetNextFail
    intro x hx
    exact hAgree (a := x) (by omega)
  change G.auxMeetLevel
      (rightBlockImage n a) (rightBlockImage n b)
      (rightBlockImage n c) (rightBlockImage n d) = s
  omega

/-- Every auxiliary meet at a source nonmarker level >=3
is transported exactly, INCLUDING source capped comparisons
and pairs containing split vertices. -/
theorem finiteTwoBlockCarrier_right_auxMeet_large
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (a b c d : Nat) (hb3 : 3 ≤ b) (hd3 : 3 ≤ d)
    (hLarge : 3 ≤ K.auxMeetLevel a b c d) :
    (finiteTwoBlockCarrier H K n m bits).auxMeetLevel
        (rightBlockImage n a) (rightBlockImage n b)
        (rightBlockImage n c) (rightBlockImage n d) =
      rightBlockImage n (K.auxMeetLevel a b c d) := by
  classical
  let G := finiteTwoBlockCarrier H K n m bits
  let s := K.auxMeetLevel a b c d
  have hs3 : 3 ≤ s := hLarge
  have hsCap : s ≤ min a c := K.auxMeetLevel_le_min a b c d
  have haGe : s ≤ a := hsCap.trans (min_le_left _ _)
  have hcGe : s ≤ c := hsCap.trans (min_le_right _ _)
  have hMon := rightBlockImage_strictMono n FH.length_ge_three
  have hTargetAt : G.SameAuxTypeBelow (rightBlockImage n s)
      (rightBlockImage n a) (rightBlockImage n b)
      (rightBlockImage n c) (rightBlockImage n d) :=
    (finiteTwoBlockCarrier_right_pair_auxType_iff
      FH FK bits s a b c d hs3 hb3 hd3).mpr
        (K.auxMeetLevel_agree a b c d)
  have hCapTarget : rightBlockImage n s ≤
      min (rightBlockImage n a) (rightBlockImage n c) := by
    have haMon := hMon.monotone haGe
    have hcMon := hMon.monotone hcGe
    omega
  have hLower : rightBlockImage n s ≤
      G.auxMeetLevel
        (rightBlockImage n a) (rightBlockImage n b)
        (rightBlockImage n c) (rightBlockImage n d) :=
    Nat.le_findGreatest hCapTarget hTargetAt
  by_cases hCapped : s = min a c
  · have hMinImage : min (rightBlockImage n a)
        (rightBlockImage n c) = rightBlockImage n s := by
      rcases le_total a c with hac | hca
      · have hsEq : s = a := by
          simpa only [min_eq_left hac] using hCapped
        rw [min_eq_left (hMon.monotone hac), hsEq]
      · have hsEq : s = c := by
          simpa only [min_eq_right hca] using hCapped
        rw [min_eq_right (hMon.monotone hca), hsEq]
    have hUpper := G.auxMeetLevel_le_min
      (rightBlockImage n a) (rightBlockImage n b)
      (rightBlockImage n c) (rightBlockImage n d)
    change G.auxMeetLevel (rightBlockImage n a)
      (rightBlockImage n b) (rightBlockImage n c)
      (rightBlockImage n d) = rightBlockImage n s
    omega
  · have hStrict : s < min a c := by omega
    have hSourceNextFail : ¬ K.SameAuxTypeBelow (s+1) a b c d := by
      intro ht
      have hCap : s + 1 ≤ min a c := by omega
      have hTooLarge : s + 1 ≤ K.auxMeetLevel a b c d :=
        Nat.le_findGreatest hCap ht
      dsimp [s] at *
      omega
    have hTargetNextFail :
        ¬ G.SameAuxTypeBelow (rightBlockImage n s + 1)
          (rightBlockImage n a) (rightBlockImage n b)
          (rightBlockImage n c) (rightBlockImage n d) := by
      intro ht
      have hNext : G.SameAuxTypeBelow (rightBlockImage n (s+1))
          (rightBlockImage n a) (rightBlockImage n b)
          (rightBlockImage n c) (rightBlockImage n d) := by
        rwa [rightBlockImage_succ_of_ge_three n s hs3]
      exact hSourceNextFail
        ((finiteTwoBlockCarrier_right_pair_auxType_iff
          FH FK bits (s+1) a b c d (by omega) hb3 hd3).mp hNext)
    have hUpper : G.auxMeetLevel
        (rightBlockImage n a) (rightBlockImage n b)
        (rightBlockImage n c) (rightBlockImage n d) <
          rightBlockImage n s + 1 := by
      by_contra hbad
      have hg : rightBlockImage n s + 1 ≤
        G.auxMeetLevel
          (rightBlockImage n a) (rightBlockImage n b)
          (rightBlockImage n c) (rightBlockImage n d) := by omega
      have hAgree := G.auxMeetLevel_agree
        (rightBlockImage n a) (rightBlockImage n b)
        (rightBlockImage n c) (rightBlockImage n d)
      apply hTargetNextFail
      intro x hx
      exact hAgree (a := x) (by omega)
    change G.auxMeetLevel (rightBlockImage n a)
      (rightBlockImage n b) (rightBlockImage n c)
      (rightBlockImage n d) = rightBlockImage n s
    omega

/-- All right-copy auxiliary pair meets are preserved numerically.
The source vertices are nonmarkers, but neither pair is required
to consist of leaves, and equality/capping are allowed. -/
theorem finiteTwoBlockCarrier_right_auxMeet_exact
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (a b c d : Nat)
    (ha3 : 3 ≤ a) (hb3 : 3 ≤ b)
    (hc3 : 3 ≤ c) (hd3 : 3 ≤ d) :
    (finiteTwoBlockCarrier H K n m bits).auxMeetLevel
        (rightBlockImage n a) (rightBlockImage n b)
        (rightBlockImage n c) (rightBlockImage n d) =
      rightBlockImage n (K.auxMeetLevel a b c d) := by
  by_cases hs : K.auxMeetLevel a b c d < 3
  · have ht := finiteTwoBlockCarrier_right_auxMeet_small
      FH FK bits a b c d ha3 hc3 hs
    have hFix := rightBlockImage_marker n
      (K.auxMeetLevel a b c d) hs
    rw [hFix]
    exact ht
  · exact finiteTwoBlockCarrier_right_auxMeet_large
      FH FK bits a b c d hb3 hd3 (by omega)

end DiaryLeafPriority
end ThreeUniformDiaries
