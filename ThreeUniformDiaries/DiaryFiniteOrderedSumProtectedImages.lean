import ThreeUniformDiaries.DiaryFiniteMeetEmbedding
import ThreeUniformDiaries.DiaryFiniteOrderedSumProtectedCopies

/-!
# Both input images in a finite ordered sum are protected pictures

The raw two-block carrier has TWO genuine increasing maps:
the identity on its left finite block and rightBlockImage n on
its translated right block. The two blocks share only markers.

This module shows that each map satisfies the reusable exact
FiniteMeetEmbedding interface (all nonmarker roles, every singleton
and full ordered-pair numerical meet, and Devlin marker 1/2).
This holds for arbitrary cross Devlin orientation bits when both
source blocks are finite V/E pre-diaries, without source S1/S2.

When the two inputs are finite DIARIES, their image nonmarker
sets therefore satisfy the exact protected S1/S2 conditions of
FiniteProtectedMeetPicture. A single chosen causal orientation
then produces a finite V/E pre-diary containing BOTH protected
copies. This is the precise mathematical input to the countable
dummy-tail plus one-pass completion theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- Entire left initial segment, including all split/leaf
mixed numerical meet comparisons, is a protected finite
meet embedding for ANY cross bit assignment. -/
theorem finiteTwoBlockCarrier_left_meetEmbedding
    (PH : FiniteRolePrediaryBlock H n)
    (PK : FiniteRolePrediaryBlock K m)
    (bits : Nat → Bool) :
    FiniteMeetEmbedding H
      (finiteTwoBlockCarrier H K n m bits) n (fun x : Nat => x) := by
  refine {
    strictMono := ?_
    marker_one := rfl
    marker_two := rfl
    leaf_iff := ?_
    oneSplit_iff := ?_
    twoSplit_iff := ?_
    oneMeet := ?_
    twoMeet := ?_
  }
  · intro a b hab
    exact hab
  · intro u _hu3 hun
    exact finiteTwoBlockCarrier_left_leaf_iff
      PH.frame PK.frame bits u hun
  · intro u _hu3 hun
    exact finiteTwoBlockCarrier_left_oneSplit_iff
      PH.frame PK.frame bits u hun
  · intro u _hu3 hun
    exact finiteTwoBlockCarrier_left_twoSplit_iff
      PH.frame PK.frame bits u hun
  · intro u v _hu3 hun _hv3 hvn
    exact finiteTwoBlockCarrier_left_oneMeet_exact
      PH.frame PK.frame bits u v hun hvn
  · intro a b c d _hab _hcd _ha3 han _hb3 hbn
        _hc3 hcn _hd3 hdn
    exact finiteTwoBlockCarrier_left_twoMeet_exact
      PH.frame PK.frame bits a b c d han hbn hcn hdn

/-- The translated right block is a protected finite meet
embedding with its actual marker-fixed increasing translation.
This is valid for all source nonmarker role combinations. -/
theorem finiteTwoBlockCarrier_right_meetEmbedding
    (PH : FiniteRolePrediaryBlock H n)
    (PK : FiniteRolePrediaryBlock K m)
    (bits : Nat → Bool) :
    FiniteMeetEmbedding K
      (finiteTwoBlockCarrier H K n m bits) m
      (rightBlockImage n) := by
  refine {
    strictMono := rightBlockImage_strictMono n PH.frame.length_ge_three
    marker_one := rightBlockImage_marker n 1 (by omega)
    marker_two := rightBlockImage_marker n 2 (by omega)
    leaf_iff := ?_
    oneSplit_iff := ?_
    twoSplit_iff := ?_
    oneMeet := ?_
    twoMeet := ?_
  }
  · intro u hu3 hum
    exact finiteTwoBlockCarrier_right_leaf_iff
      PH.frame PK.frame bits u hu3 hum
  · intro u hu3 hum
    exact finiteTwoBlockCarrier_right_oneSplit_iff
      PH.frame PK.frame bits u hu3 hum
  · intro u hu3 hum
    exact finiteTwoBlockCarrier_right_twoSplit_iff
      PH.frame PK.frame bits u hu3 hum
  · intro u v hu3 hum hv3 hvm
    exact finiteTwoBlockCarrier_right_oneMeet_exact_all
      PH.frame PK PH.permitted_edge bits u v hu3 hum hv3 hvm
  · intro a b c d hab hcd ha3 ham hb3 hbm hc3 hcm hd3 hdm
    exact finiteTwoBlockCarrier_right_twoMeet_exact_all
      PH.frame PK PH.permitted_edge bits
      a b c d hab hcd ha3 ham hb3 hbm hc3 hcm hd3 hdm

/-- Both genuine finite DIARY copies remain exact S1/S2
protected subpictures of the finite ordered-sum pre-diary, for
any cross orientation bits. -/
theorem finiteTwoBlockCarrier_left_protectedPicture
    (DH : FiniteRoleDiaryBlock H n)
    (DK : FiniteRoleDiaryBlock K m)
    (bits : Nat → Bool) :
    FiniteProtectedMeetPicture
      (finiteTwoBlockCarrier H K n m bits)
      (finiteMeetImage n (fun x : Nat => x)) :=
  (finiteTwoBlockCarrier_left_meetEmbedding
    DH.prediary DK.prediary bits).protected_picture DH

theorem finiteTwoBlockCarrier_right_protectedPicture
    (DH : FiniteRoleDiaryBlock H n)
    (DK : FiniteRoleDiaryBlock K m)
    (bits : Nat → Bool) :
    FiniteProtectedMeetPicture
      (finiteTwoBlockCarrier H K n m bits)
      (finiteMeetImage m (rightBlockImage n)) :=
  (finiteTwoBlockCarrier_right_meetEmbedding
    DH.prediary DK.prediary bits).protected_picture DK

/-- ONE finite ordered sum contains two protected diary inputs,
disjoint outside the three shared markers, and already satisfies
all bounded V/E pre-diary conditions. This is not a final diary
(S1/S2 comparisons across different blocks can fail). -/
theorem exists_finiteTwoBlock_sum_protectedPictures
    (DH : FiniteRoleDiaryBlock H n)
    (DK : FiniteRoleDiaryBlock K m) :
    ∃ bits : Nat → Bool,
      FiniteRolePrediaryBlock
        (finiteTwoBlockCarrier H K n m bits)
        (finiteTwoBlockLength n m) ∧
      FiniteProtectedMeetPicture
        (finiteTwoBlockCarrier H K n m bits)
        (finiteMeetImage n (fun x : Nat => x)) ∧
      FiniteProtectedMeetPicture
        (finiteTwoBlockCarrier H K n m bits)
        (finiteMeetImage m (rightBlockImage n)) := by
  obtain ⟨bits, P⟩ :=
    exists_finiteTwoBlock_sum_prediary DH.prediary DK
  exact ⟨bits,P,
    finiteTwoBlockCarrier_left_protectedPicture DH DK bits,
    finiteTwoBlockCarrier_right_protectedPicture DH DK bits⟩

end DiaryLeafPriority
end ThreeUniformDiaries
