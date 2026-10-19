import ThreeUniformDiaries.DiaryFiniteMeetEmbedding
import ThreeUniformDiaries.DiaryFiniteOrderedSumProtectedCopies

/-!
# Actual induced meet embeddings in protected two-block sums

The finite ordered-sum theorem already constructs both copies and
preserves all their singleton/full-pair meets. We package the maps
as genuine finite meet embeddings in the strengthened interface:
they fix ALL three markers, preserve and reflect the ordered
ternary relation, reflect marker-derived roles, and preserve
every numerical one- and full two-meet.

The left copy is the literal identity on the initial segment.
The right copy is the strictly increasing rightBlockImage map
which fixes markers and translates nonmarker vertices.
No false global RoleDiary assumption on the unused Nat tail.

The resulting two-copy theorem will be an input to finite-family
iteration and countable protected completion; it does not assert
every-flip target absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- Every protected finite sum contains the left finite block as
a genuine induced and meet-preserving finite embedding, not
merely a numerical meet map. -/
theorem FiniteSumProtectedCopies.left_meetEmbedding
    (PH : FiniteRolePrediaryBlock H n)
    (PK : FiniteRolePrediaryBlock K m)
    (bits : Nat → Bool)
    (P : FiniteSumProtectedCopies H K n m bits) :
    FiniteMeetEmbedding H (finiteTwoBlockCarrier H K n m bits)
      n (fun x : Nat => x) := by
  refine {
    strictMono := ?_
    marker_zero := rfl
    marker_one := rfl
    marker_two := rfl
    edge_iff := ?_
    leaf_iff := ?_
    oneSplit_iff := ?_
    twoSplit_iff := ?_
    oneMeet := ?_
    twoMeet := ?_
  }
  · intro x y hxy
    exact hxy
  · intro a b c _hab _hbc hc
    exact finiteTwoBlockCarrier_left_edge_iff
      PH.frame PK.frame bits a b c hc
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
    exact P.left_oneMeet u v hun hvn
  · intro a b c d _hab _hcd _ha3 han _hb3 hbn _hc3 hcn _hd3 hdn
    exact P.left_twoMeet a b c d han hbn hcn hdn

/-- Every protected finite sum contains the translated right
finite block as an increasing induced meet embedding, fixing
0,1,2 exactly, including reflected source nonedges. -/
theorem FiniteSumProtectedCopies.right_meetEmbedding
    (PH : FiniteRolePrediaryBlock H n)
    (PK : FiniteRolePrediaryBlock K m)
    (bits : Nat → Bool)
    (P : FiniteSumProtectedCopies H K n m bits) :
    FiniteMeetEmbedding K (finiteTwoBlockCarrier H K n m bits)
      m (rightBlockImage n) := by
  refine {
    strictMono := rightBlockImage_strictMono n PH.frame.length_ge_three
    marker_zero := rightBlockImage_marker n 0 (by omega)
    marker_one := rightBlockImage_marker n 1 (by omega)
    marker_two := rightBlockImage_marker n 2 (by omega)
    edge_iff := ?_
    leaf_iff := ?_
    oneSplit_iff := ?_
    twoSplit_iff := ?_
    oneMeet := ?_
    twoMeet := ?_
  }
  · intro a b c _hab _hbc _hc
    exact finiteTwoBlockCarrier_right_edge_iff_all
      PH.frame PK.frame bits a b c
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
    exact P.right_oneMeet u v hu3 hum hv3 hvm
  · intro a b c d hab hcd ha3 ham hb3 hbm hc3 hcm hd3 hdm
    exact P.right_twoMeet a b c d hab hcd
      ha3 ham hb3 hbm hc3 hcm hd3 hdm

/-- The checked protected two-block sum provides BOTH actual
induced finite meet embeddings for one common target and one
causally selected cross-marker orientation. The left input may
already be a finite V/E pre-diary. -/
theorem exists_finiteTwoBlock_both_meetEmbeddings
    (PH : FiniteRolePrediaryBlock H n)
    (DK : FiniteRoleDiaryBlock K m) :
    ∃ bits : Nat → Bool,
      FiniteRolePrediaryBlock
        (finiteTwoBlockCarrier H K n m bits)
        (finiteTwoBlockLength n m) ∧
      FiniteMeetEmbedding H (finiteTwoBlockCarrier H K n m bits)
        n (fun x : Nat => x) ∧
      FiniteMeetEmbedding K (finiteTwoBlockCarrier H K n m bits)
        m (rightBlockImage n) := by
  obtain ⟨bits, P⟩ := exists_finiteTwoBlock_sum_protected PH DK
  refine ⟨bits, P.target_prediary, ?_, ?_⟩
  · exact P.left_meetEmbedding PH DK.prediary bits
  · exact P.right_meetEmbedding PH DK.prediary bits

/-- In particular the right finite input diary is protected as
a genuine S1/S2 finite nonmarker picture in the common target. -/
theorem exists_finiteTwoBlock_right_protectedPicture
    (PH : FiniteRolePrediaryBlock H n)
    (DK : FiniteRoleDiaryBlock K m) :
    ∃ bits : Nat → Bool,
      FiniteRolePrediaryBlock
        (finiteTwoBlockCarrier H K n m bits)
        (finiteTwoBlockLength n m) ∧
      FiniteProtectedMeetPicture
        (finiteTwoBlockCarrier H K n m bits)
        (finiteMeetImage m (rightBlockImage n)) := by
  obtain ⟨bits, P, _ELeft, ERight⟩ :=
    exists_finiteTwoBlock_both_meetEmbeddings PH DK
  exact ⟨bits, P, ERight.protected_picture DK⟩

end DiaryLeafPriority
end ThreeUniformDiaries
