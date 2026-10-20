import ThreeUniformDiaries.DiaryFiniteSupportProtectedOneMeet

/-!
# Every protected full pair meet survives finite support extraction

Let a prescribed finite diary be embedded into a countable ambient
diary by a genuine finite meet embedding. Keep the entire image of
the finite source, and compress to any finite support containing it.

For full ordered-pair types the source first disagreement at its
meet level is one of three tests: the first singleton coordinate,
the second singleton coordinate, or the pair auxiliary coordinate.
The first two are preserved by the already checked protected
singleton-meet transport. The third is a literal source triple
whose full image is retained, so inducedness preserves its bit.

This proves exact numerical full pair meets of arbitrary source
nonmarker ordered pairs, even when split vertices occur in them.
It does not assert inverse type transport for arbitrary vertices
of the ambient finite support.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A G : Ordered3Graph Nat} {S : Finset Nat}
variable {n : Nat} {f : Nat → Nat}

/-- Every complete protected source pair meet, including mixed
leaf/split tuples and capped cases, has the exact target level
in the increasing finite induced restriction. -/
theorem finiteSupportLift_twoMeet_exact
    (E : FiniteMeetEmbedding A G n f)
    (hRange : ∀ u, u < n → f u ∈ S)
    (a b c d : Nat) (hab : a < b) (hcd : c < d)
    (ha3 : 3 ≤ a) (ha : a < n)
    (hb3 : 3 ≤ b) (hb : b < n)
    (hc3 : 3 ≤ c) (hc : c < n)
    (hd3 : 3 ≤ d) (hd : d < n) :
    (finiteSupportGraph G S).twoMeetLevel
      (finiteSupportLift S n f a) (finiteSupportLift S n f b)
      (finiteSupportLift S n f c) (finiteSupportLift S n f d) =
    finiteSupportLift S n f (A.twoMeetLevel a b c d) := by
  classical
  let H := finiteSupportGraph G S
  let g := finiteSupportLift S n f
  let m := A.twoMeetLevel a b c d
  have hmBound : m ≤ min a c := A.twoMeetLevel_le_min a b c d
  have hm : m < n := by omega
  have hmA : m ≤ a := hmBound.trans (min_le_left _ _)
  have hmC : m ≤ c := hmBound.trans (min_le_right _ _)
  have hg : StrictMono g :=
    finiteSupportLift_strictMono S n f E.strictMono hRange
  have hgmA : g m ≤ g a := hg.monotone hmA
  have hgmC : g m ≤ g c := hg.monotone hmC
  have sm := finiteSupportLift_spec S n f hRange m hm
  have sa := finiteSupportLift_spec S n f hRange a ha
  have sb := finiteSupportLift_spec S n f hRange b hb
  have sc := finiteSupportLift_spec S n f hRange c hc
  have sd := finiteSupportLift_spec S n f hRange d hd
  have hOldMeet : G.twoMeetLevel (f a) (f b) (f c) (f d) = f m := by
    dsimp [m]
    exact E.twoMeet a b c d hab hcd ha3 ha hb3 hb hc3 hc hd3 hd
  have hOldAt : G.SameTwoTypeBelow (f m) (f a) (f b) (f c) (f d) := by
    rw [← hOldMeet]
    exact G.twoMeetLevel_agree (f a) (f b) (f c) (f d)
  have hNewAt : H.SameTwoTypeBelow
      (g m) (g a) (g b) (g c) (g d) := by
    apply finiteSupportGraph_twoType_of_original
      (G := G) (S := S) (g m) (g a) (g b) (g c) (g d)
      sm.1 sa.1 sb.1 sc.1 sd.1 (hg hab) (hg hcd) hgmA hgmC
    change G.SameTwoTypeBelow
      (finiteSupportIndex S (finiteSupportLift S n f m))
      (finiteSupportIndex S (finiteSupportLift S n f a))
      (finiteSupportIndex S (finiteSupportLift S n f b))
      (finiteSupportIndex S (finiteSupportLift S n f c))
      (finiteSupportIndex S (finiteSupportLift S n f d))
    rw [sm.2,sa.2,sb.2,sc.2,sd.2]
    exact hOldAt
  have hLower : g m ≤ H.twoMeetLevel (g a) (g b) (g c) (g d) :=
    Nat.le_findGreatest (le_min hgmA hgmC) hNewAt
  have hUpper : H.twoMeetLevel (g a) (g b) (g c) (g d) ≤ g m := by
    by_cases hCap : m = min a c
    · have hMin : g m = min (g a) (g c) := by
        rcases le_total a c with hac | hca
        · have hmEq : m = a := by
            simpa only [min_eq_left hac] using hCap
          rw [hmEq,min_eq_left (hg.monotone hac)]
        · have hmEq : m = c := by
            simpa only [min_eq_right hca] using hCap
          rw [hmEq,min_eq_right (hg.monotone hca)]
      have hBound := H.twoMeetLevel_le_min (g a) (g b) (g c) (g d)
      omega
    · have hStrict : m < min a c := by omega
      have hma : m < a := by omega
      have hmc : m < c := by omega
      have hAt : A.SameTwoTypeBelow m a b c d :=
        A.twoMeetLevel_agree a b c d
      have hFail : ¬ A.SameTwoTypeBelow (m + 1) a b c d := by
        intro hNext
        have hTooLarge : m + 1 ≤ A.twoMeetLevel a b c d :=
          Nat.le_findGreatest (by omega) hNext
        dsimp [m] at hTooLarge
        omega
      have hCases :
          ¬ A.SameOneTypeBelow (m + 1) a c ∨
          ¬ A.SameOneTypeBelow (m + 1) b d ∨
          ¬ A.SameAuxTypeBelow (m + 1) a b c d := by
        by_cases hFirst : A.SameOneTypeBelow (m + 1) a c
        · by_cases hSecond : A.SameOneTypeBelow (m + 1) b d
          · exact Or.inr (Or.inr (by
              intro hAux
              exact hFail ⟨hFirst,hSecond,hAux⟩))
          · exact Or.inr (Or.inl hSecond)
        · exact Or.inl hFirst
      rcases hCases with hFirst | hSecond | hAux
      · have hSourceOne : A.oneMeetLevel a c = m := by
          have hLow : m ≤ A.oneMeetLevel a c :=
            Nat.le_findGreatest (by omega) hAt.1
          have hHigh : A.oneMeetLevel a c ≤ m := by
            by_contra hbad
            have hSucc : A.SameOneTypeBelow (m + 1) a c := by
              have hAgree := A.oneMeetLevel_agree a c
              intro x y hxy hy
              exact hAgree hxy (by omega)
            exact hFirst hSucc
          omega
        have hTargetOne : H.oneMeetLevel (g a) (g c) = g m := by
          rw [finiteSupportLift_oneMeet_exact
            E hRange a c ha3 ha hc3 hc, hSourceOne]
        have hT := H.twoMeetLevel_agree (g a) (g b) (g c) (g d)
        have hBound := H.twoMeetLevel_le_min (g a) (g b) (g c) (g d)
        have hLe : H.twoMeetLevel (g a) (g b) (g c) (g d) ≤
            H.oneMeetLevel (g a) (g c) :=
          Nat.le_findGreatest hBound hT.1
        rw [hTargetOne] at hLe
        exact hLe
      · have hSourceOne : A.oneMeetLevel b d = m := by
          have hBoundSecond : m ≤ min b d := by
            apply le_min
            · omega
            · omega
          have hLow : m ≤ A.oneMeetLevel b d :=
            Nat.le_findGreatest hBoundSecond hAt.2.1
          have hHigh : A.oneMeetLevel b d ≤ m := by
            by_contra hbad
            have hSucc : A.SameOneTypeBelow (m + 1) b d := by
              have hAgree := A.oneMeetLevel_agree b d
              intro x y hxy hy
              exact hAgree hxy (by omega)
            exact hSecond hSucc
          omega
        have hTargetOne : H.oneMeetLevel (g b) (g d) = g m := by
          rw [finiteSupportLift_oneMeet_exact
            E hRange b d hb3 hb hd3 hd, hSourceOne]
        have hT := H.twoMeetLevel_agree (g a) (g b) (g c) (g d)
        have hTargetCap := H.twoMeetLevel_le_min (g a) (g b) (g c) (g d)
        have hBoundSecond :
            H.twoMeetLevel (g a) (g b) (g c) (g d) ≤
              min (g b) (g d) := by
          apply le_min
          · exact (hTargetCap.trans (min_le_left _ _)).trans (hg hab).le
          · exact (hTargetCap.trans (min_le_right _ _)).trans (hg hcd).le
        have hLe : H.twoMeetLevel (g a) (g b) (g c) (g d) ≤
            H.oneMeetLevel (g b) (g d) :=
          Nat.le_findGreatest hBoundSecond hT.2.1
        rw [hTargetOne] at hLe
        exact hLe
      · have hBit : ¬ (A.edge m a b ↔ A.edge m c d) := by
          intro hSame
          exact hAux ((A.sameAuxTypeBelow_succ_iff m a b c d).mpr
            ⟨hAt.2.2,hSame⟩)
        have hEqAB : H.edge (g m) (g a) (g b) ↔ A.edge m a b :=
          finiteSupportLift_edge_iff E hRange m a b hma hab hb
        have hEqCD : H.edge (g m) (g c) (g d) ↔ A.edge m c d :=
          finiteSupportLift_edge_iff E hRange m c d hmc hcd hd
        have hDifferent :
            ¬ (H.edge (g m) (g a) (g b) ↔
               H.edge (g m) (g c) (g d)) := by
          intro hSame
          exact hBit (hEqAB.symm.trans (hSame.trans hEqCD))
        by_contra hToo
        have hLater : g m < H.twoMeetLevel (g a) (g b) (g c) (g d) := by
          omega
        exact hDifferent
          ((H.twoMeetLevel_agree (g a) (g b) (g c) (g d)).2.2 hLater)
  change H.twoMeetLevel (g a) (g b) (g c) (g d) = g m
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
