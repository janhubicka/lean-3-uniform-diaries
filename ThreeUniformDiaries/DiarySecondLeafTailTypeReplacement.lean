import ThreeUniformDiaries.DiaryTailSingletonTypeCone
import ThreeUniformDiaries.DiarySecondLeafFixedCandidateConverse

/-!
# Tail replacement at the SECOND source diary leaf

The verified fixed-v criterion at the second selected source leaf
uses exactly: a right one-split orientation bit, two inequalities
constraining the split level relative to the fixed old leaf,
and a final numerical lower bound on the new leaf image.

Once a genuine target leaf v₀ is known to give a reserved successor,
ANY later target leaf v in the prescribed outer range having
the SAME singleton type below f(a)+1 gives another successor.

The proof is substantive: the capped singleton meet with the
fixed old image f(a) remains exactly the same, and the right
marker/split incidence (0,r,v) is a single test below that cut.
All three numerical gaps are preserved, the last by v≥v₀.

This proves closure of the SECOND-LEAF solution set under a
particular actual mixed unary type cone. It DOES NOT assert
that this cone contains a single other prescribed-range leaf,
nor that one chosen leaf remains persistent at every later stage.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For exactly one previously selected source leaf a, a reserved
successor sending the next source leaf m to v₀ may be replaced by
any later target leaf v with identical singleton type below f(a)+1,
provided v is itself a genuine target leaf in the outer F-range. -/
theorem RoleDiary.second_leaf_successor_of_same_tail_type
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (F f : Nat → Nat) (a m v₀ v : Nat)
    (ha : IsLeaf H a) (hm : IsLeaf H m) (ham : a < m)
    (hOld : countableDiaryLeafPrefix H m = {a})
    (P : ReservedDiaryStage H K F m f)
    (hv₀Leaf : IsLeaf K v₀)
    (hv₀Range : ∃ t : Nat, v₀ = F t)
    (hOldSuccessor : ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1) g ∧
      (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m → g u = f u) ∧
      g m = v₀)
    (hvLeaf : IsLeaf K v)
    (hvRange : ∃ t : Nat, v = F t)
    (hvLater : v₀ ≤ v)
    (hSame : K.SameOneTypeBelow (f a + 1) v₀ v) :
    ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1) g ∧
      (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m → g u = f u) ∧
      g m = v := by
  let s := H.oneMeetLevel a m
  let w := f a
  let r₀ := K.oneMeetLevel w v₀
  let r := K.oneMeetLevel w v
  have hCriteria :=
    (DH.second_leaf_fixed_v_reserved_successor_iff
      DK F f a m v₀ ha hm ham hOld P hv₀Leaf hv₀Range).mp
        hOldSuccessor
  obtain ⟨hBit₀,hGap₁,hGap₂,hGap₃⟩ := hCriteria
  have hwLtV₀ : w < v₀ := by
    have hStep : 0 < m - a := Nat.sub_pos_of_lt ham
    dsimp [w] at hGap₃ ⊢
    omega
  have hwLtV : w < v := lt_of_lt_of_le hwLtV₀ hvLater
  have hMeet : r₀ = r :=
    oneMeetLevel_eq_of_sameOneTypeBelow_cut
      K (w + 1) w v₀ v (by omega) hwLtV₀ hwLtV
        (by simpa only [w] using hSame)
  have hRBound : r₀ ≤ w :=
    (K.oneMeetLevel_le_min w v₀).trans (min_le_left _ _)
  have hSOne : IsOneSplit H s :=
    DH.singleton_meets a m ha hm (ne_of_lt ham)
  have hrPos : 0 < r₀ := by
    have hs3 : 3 ≤ s := hSOne.1
    dsimp [s,r₀,w] at hGap₁ ⊢
    omega
  have hRightBit : K.edge 0 r₀ v₀ ↔ K.edge 0 r₀ v :=
    hSame hrPos (by simpa only [r₀,w] using
      (show K.oneMeetLevel (f a) v₀ < f a + 1 by omega))
  have hNewBit :
      H.edge 0 s m ↔ K.edge 0 r v := by
    calc
      H.edge 0 s m ↔ K.edge 0 r₀ v₀ := hBit₀
      _ ↔ K.edge 0 r₀ v := hRightBit
      _ ↔ K.edge 0 r v := by rw [hMeet]
  have hGap₃New : w + (m - a) ≤ v :=
    hGap₃.trans hvLater
  apply (DH.second_leaf_fixed_v_reserved_successor_iff
    DK F f a m v ha hm ham hOld P hvLeaf hvRange).mpr
  exact ⟨hNewBit,
    by simpa only [r,←hMeet] using hGap₁,
    by simpa only [r,←hMeet] using hGap₂,
    hGap₃New⟩

end DiaryLeafPriority
end ThreeUniformDiaries
