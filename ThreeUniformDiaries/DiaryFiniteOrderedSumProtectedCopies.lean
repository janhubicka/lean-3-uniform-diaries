import ThreeUniformDiaries.DiaryFiniteOrderedSumFullPrediary
import ThreeUniformDiaries.DiaryFiniteOrderedSumLeftExactMeets
import ThreeUniformDiaries.DiaryFiniteOrderedSumRightAllTwoMeets

/-!
# Two genuinely protected copies in a finite ordered-sum pre-diary

The verified finite ordered-sum theorem produces a bounded V/E
pre-diary containing two induced copies of finite input diaries,
with only the distinguished markers 0,1,2 identified.
The left input may itself be a previously constructed pre-diary. For a diary
embedding we also need preservation of the NUMERICAL singleton
and full pair-type meets of all nonmarker vertices of each copy.

For the left block all exact meets follow from induced initial
segment type transport. For the right block the auxiliary and both
singleton coordinates are preserved and their minimum yields the
complete two-meet. The existence theorem packages a SINGLE chosen
cross Devlin orientation satisfying all finite pre-diary axioms
AND protecting BOTH copies simultaneously.

No statement about a full RolePrediary on Nat or every-flip target
absorption is included. The next independent step is the countable
dummy-tail extension, preserving this finite protected picture.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- A finite V/E ordered sum with its two input copies protected
at the exact numerical singleton and full two-type meet levels.
All right-copy vertices here are NONMARKERS; the three common
markers are identified and kept unchanged by both source maps. -/
structure FiniteSumProtectedCopies
    (H K : Ordered3Graph Nat) (n m : Nat)
    (bits : Nat → Bool) : Prop where
  target_prediary :
    FiniteRolePrediaryBlock
      (finiteTwoBlockCarrier H K n m bits)
      (finiteTwoBlockLength n m)
  left_oneMeet :
    ∀ u v : Nat, u < n → v < n →
      (finiteTwoBlockCarrier H K n m bits).oneMeetLevel u v =
        H.oneMeetLevel u v
  left_twoMeet :
    ∀ a b c d : Nat, a < n → b < n → c < n → d < n →
      (finiteTwoBlockCarrier H K n m bits).twoMeetLevel a b c d =
        H.twoMeetLevel a b c d
  right_oneMeet :
    ∀ u v : Nat, 3 ≤ u → u < m → 3 ≤ v → v < m →
      (finiteTwoBlockCarrier H K n m bits).oneMeetLevel
        (rightBlockImage n u) (rightBlockImage n v) =
      rightBlockImage n (K.oneMeetLevel u v)
  right_twoMeet :
    ∀ a b c d : Nat, a < b → c < d →
      3 ≤ a → a < m → 3 ≤ b → b < m →
      3 ≤ c → c < m → 3 ≤ d → d < m →
      (finiteTwoBlockCarrier H K n m bits).twoMeetLevel
        (rightBlockImage n a) (rightBlockImage n b)
        (rightBlockImage n c) (rightBlockImage n d) =
      rightBlockImage n (K.twoMeetLevel a b c d)

/-- The complete protected TWO-COPY finite ordered-sum theorem:
one causal Boolean orientation yields a bounded V/E pre-diary
with an induced finite pre-diary LEFT copy and finite diary RIGHT
copy, preserving all their numerical one- and full two-meets. -/
theorem exists_finiteTwoBlock_sum_protected
    (PH : FiniteRolePrediaryBlock H n)
    (DK : FiniteRoleDiaryBlock K m) :
    ∃ bits : Nat → Bool, FiniteSumProtectedCopies H K n m bits := by
  obtain ⟨bits, P⟩ := exists_finiteTwoBlock_sum_prediary PH DK
  refine ⟨bits, {
    target_prediary := P
    left_oneMeet := ?_
    left_twoMeet := ?_
    right_oneMeet := ?_
    right_twoMeet := ?_
  }⟩
  · intro u v hun hvn
    exact finiteTwoBlockCarrier_left_oneMeet_exact
      PH.frame DK.prediary.frame bits u v hun hvn
  · intro a b c d han hbn hcn hdn
    exact finiteTwoBlockCarrier_left_twoMeet_exact
      PH.frame DK.prediary.frame bits
      a b c d han hbn hcn hdn
  · intro u v hu3 hum hv3 hvm
    exact finiteTwoBlockCarrier_right_oneMeet_exact_all
      PH.frame DK.prediary
      PH.permitted_edge bits
      u v hu3 hum hv3 hvm
  · intro a b c d hab hcd
      ha3 ham hb3 hbm hc3 hcm hd3 hdm
    exact finiteTwoBlockCarrier_right_twoMeet_exact_all
      PH.frame DK.prediary
      PH.permitted_edge bits
      a b c d hab hcd ha3 ham hb3 hbm hc3 hcm hd3 hdm

end DiaryLeafPriority
end ThreeUniformDiaries
