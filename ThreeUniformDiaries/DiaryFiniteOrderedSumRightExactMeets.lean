import ThreeUniformDiaries.DiaryFiniteOrderedSumRightPairTransport

/-!
# Exact meet levels for right-block witnesses in finite ordered sums

Right-block singleton and full pair-type agreement is transported
both ways at every translated right cut (PRs #670 and #671).
At source cut s >= 3, its translated position is a consecutive
target level: image(s+1) = image(s)+1.

A source meet at a strict non-capped cut s is therefore exactly
the target meet at image(s): equality through the cut transports,
and inequality at the very next cut also transports. The induced
right copy supplies exact role and edge reflection, so these
are the numerical ingredients for right-side finite V1/V2 witnesses.

No ambient V/E/S source structure or global target pre-diary is
assumed. The proof requires only the stated strict (non-capped)
source meeting level, leaf roles, finite support and right E shapes.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- The translated right block has no gaps between successive
original nonmarker levels. -/
theorem rightBlockImage_succ_of_ge_three
    (n s : Nat) (hs3 : 3 ≤ s) :
    rightBlockImage n (s + 1) = rightBlockImage n s + 1 := by
  have hNot : ¬ s < 3 := by omega
  have hNotSucc : ¬ s + 1 < 3 := by omega
  simp only [rightBlockImage, if_neg hNot, if_neg hNotSucc]
  omega

/-- Any strict source first singleton meet at a right-block level
s >=3 is literally transported to the target image of s.
The source need not be a full diary. -/
theorem finiteTwoBlockCarrier_right_oneMeet_exact
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hshape : ∀ x y z : Nat, K.edge x y z →
      PermittedDiaryEdge K x y z)
    (bits : Nat → Bool)
    (s a b : Nat) (hs3 : 3 ≤ s)
    (ha3 : 3 ≤ a) (ham : a < m) (haLeaf : IsLeaf K a)
    (hb3 : 3 ≤ b) (hbm : b < m) (hbLeaf : IsLeaf K b)
    (hsa : s < a) (hsb : s < b)
    (hMeet : K.oneMeetLevel a b = s) :
    (finiteTwoBlockCarrier H K n m bits).oneMeetLevel
        (rightBlockImage n a) (rightBlockImage n b) =
      rightBlockImage n s := by
  classical
  let G := finiteTwoBlockCarrier H K n m bits
  have hn3 : 3 ≤ n := FH.length_ge_three
  have hSourceAt : K.SameOneTypeBelow s a b := by
    rw [← hMeet]
    exact K.oneMeetLevel_agree a b
  have hSourceNextFail : ¬ K.SameOneTypeBelow (s + 1) a b := by
    intro hNext
    have hCap : s + 1 ≤ min a b := by omega
    have hGreatest : s + 1 ≤ K.oneMeetLevel a b :=
      Nat.le_findGreatest hCap hNext
    omega
  have hTargetAt :
      G.SameOneTypeBelow (rightBlockImage n s)
        (rightBlockImage n a) (rightBlockImage n b) :=
    (finiteTwoBlockCarrier_right_leaf_oneType_iff
      FH FK hshape bits s a b hs3 ha3 ham haLeaf
        hb3 hbm hbLeaf).mpr hSourceAt
  have hTargetNextFail :
      ¬ G.SameOneTypeBelow (rightBlockImage n s + 1)
          (rightBlockImage n a) (rightBlockImage n b) := by
    intro hNext
    have hStep :
        G.SameOneTypeBelow (rightBlockImage n (s + 1))
          (rightBlockImage n a) (rightBlockImage n b) := by
      rwa [rightBlockImage_succ_of_ge_three n s hs3]
    exact hSourceNextFail
      ((finiteTwoBlockCarrier_right_leaf_oneType_iff
        FH FK hshape bits (s + 1) a b
        (by omega) ha3 ham haLeaf hb3 hbm hbLeaf).mp hStep)
  have hMon := rightBlockImage_strictMono n hn3
  have hsaTarget : rightBlockImage n s < rightBlockImage n a :=
    hMon hsa
  have hsbTarget : rightBlockImage n s < rightBlockImage n b :=
    hMon hsb
  have hCap :
      rightBlockImage n s ≤
        min (rightBlockImage n a) (rightBlockImage n b) := by omega
  have hLower :
      rightBlockImage n s ≤
        G.oneMeetLevel (rightBlockImage n a)
          (rightBlockImage n b) :=
    Nat.le_findGreatest hCap hTargetAt
  have hUpper :
      G.oneMeetLevel (rightBlockImage n a)
        (rightBlockImage n b) < rightBlockImage n s + 1 := by
    by_contra hNot
    have hGe :
        rightBlockImage n s + 1 ≤
          G.oneMeetLevel (rightBlockImage n a)
            (rightBlockImage n b) := by omega
    have hAgree :=
      G.oneMeetLevel_agree (rightBlockImage n a)
        (rightBlockImage n b)
    have hNext :
        G.SameOneTypeBelow (rightBlockImage n s + 1)
          (rightBlockImage n a) (rightBlockImage n b) := by
      intro x y hxy hy
      exact hAgree hxy (by omega)
    exact hTargetNextFail hNext
  omega

/-- Exact strict full ordered-pair meet transport for two genuine
right leaf pairs. Source and target pairs may share vertices;
the only relevant non-capping assumptions are s<a and s<c. -/
theorem finiteTwoBlockCarrier_right_twoMeet_exact
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hshape : ∀ x y z : Nat, K.edge x y z →
      PermittedDiaryEdge K x y z)
    (bits : Nat → Bool)
    (s a b c d : Nat) (hs3 : 3 ≤ s)
    (ha3 : 3 ≤ a) (ham : a < m) (haLeaf : IsLeaf K a)
    (hb3 : 3 ≤ b) (hbm : b < m) (hbLeaf : IsLeaf K b)
    (hc3 : 3 ≤ c) (hcm : c < m) (hcLeaf : IsLeaf K c)
    (hd3 : 3 ≤ d) (hdm : d < m) (hdLeaf : IsLeaf K d)
    (hsa : s < a) (hsc : s < c)
    (hMeet : K.twoMeetLevel a b c d = s) :
    (finiteTwoBlockCarrier H K n m bits).twoMeetLevel
        (rightBlockImage n a) (rightBlockImage n b)
        (rightBlockImage n c) (rightBlockImage n d) =
      rightBlockImage n s := by
  classical
  let G := finiteTwoBlockCarrier H K n m bits
  have hn3 : 3 ≤ n := FH.length_ge_three
  have hSourceAt : K.SameTwoTypeBelow s a b c d := by
    rw [← hMeet]
    exact K.twoMeetLevel_agree a b c d
  have hSourceNextFail : ¬ K.SameTwoTypeBelow (s + 1) a b c d := by
    intro hNext
    have hCap : s + 1 ≤ min a c := by omega
    have hGreatest : s + 1 ≤ K.twoMeetLevel a b c d :=
      Nat.le_findGreatest hCap hNext
    omega
  have hTargetAt :
      G.SameTwoTypeBelow (rightBlockImage n s)
        (rightBlockImage n a) (rightBlockImage n b)
        (rightBlockImage n c) (rightBlockImage n d) :=
    (finiteTwoBlockCarrier_right_leaf_twoType_iff
      FH FK hshape bits s a b c d hs3
      ha3 ham haLeaf hb3 hbm hbLeaf
      hc3 hcm hcLeaf hd3 hdm hdLeaf).mpr hSourceAt
  have hTargetNextFail :
      ¬ G.SameTwoTypeBelow (rightBlockImage n s + 1)
          (rightBlockImage n a) (rightBlockImage n b)
          (rightBlockImage n c) (rightBlockImage n d) := by
    intro hNext
    have hStep :
        G.SameTwoTypeBelow (rightBlockImage n (s + 1))
          (rightBlockImage n a) (rightBlockImage n b)
          (rightBlockImage n c) (rightBlockImage n d) := by
      rwa [rightBlockImage_succ_of_ge_three n s hs3]
    exact hSourceNextFail
      ((finiteTwoBlockCarrier_right_leaf_twoType_iff
        FH FK hshape bits (s + 1) a b c d
        (by omega) ha3 ham haLeaf hb3 hbm hbLeaf
        hc3 hcm hcLeaf hd3 hdm hdLeaf).mp hStep)
  have hMon := rightBlockImage_strictMono n hn3
  have hsaTarget : rightBlockImage n s < rightBlockImage n a :=
    hMon hsa
  have hscTarget : rightBlockImage n s < rightBlockImage n c :=
    hMon hsc
  have hCap :
      rightBlockImage n s ≤
        min (rightBlockImage n a) (rightBlockImage n c) := by omega
  have hLower :
      rightBlockImage n s ≤
        G.twoMeetLevel (rightBlockImage n a)
          (rightBlockImage n b) (rightBlockImage n c)
          (rightBlockImage n d) :=
    Nat.le_findGreatest hCap hTargetAt
  have hUpper :
      G.twoMeetLevel (rightBlockImage n a)
        (rightBlockImage n b) (rightBlockImage n c)
        (rightBlockImage n d) < rightBlockImage n s + 1 := by
    by_contra hNot
    have hGe :
        rightBlockImage n s + 1 ≤
          G.twoMeetLevel (rightBlockImage n a)
            (rightBlockImage n b) (rightBlockImage n c)
            (rightBlockImage n d) := by omega
    have hAgree :=
      G.twoMeetLevel_agree
        (rightBlockImage n a) (rightBlockImage n b)
        (rightBlockImage n c) (rightBlockImage n d)
    have hNext :
        G.SameTwoTypeBelow (rightBlockImage n s + 1)
          (rightBlockImage n a) (rightBlockImage n b)
          (rightBlockImage n c) (rightBlockImage n d) := by
      refine ⟨?_, ?_, ?_⟩
      · intro x y hxy hy
        exact hAgree.1 hxy (by omega)
      · intro x y hxy hy
        exact hAgree.2.1 hxy (by omega)
      · intro x hx
        exact hAgree.2.2 (by omega)
    exact hTargetNextFail hNext
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
