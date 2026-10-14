import ThreeUniformDiaries.DiaryFullRoleDefinition
import ThreeUniformDiaries.DiaryPreembeddingTwoSplit

/-!
# The capped-pair case in the lower-bound pre-embedding

The manuscript's final check for leaf-pair meets has three cases:
a 2-split, the first marker, and a capped meet. The 2-split is
treated by the actual I3 pre-embedding calculation, while the
marker case requires global orientation synchronisation.

For the capped case we verify an important source reduction:
two ordered pairs of diary leaves whose full 2-type meet is capped
at the minimum of their first coordinates MUST have exactly the
same first leaf. If their first leaves differed, S1 would make
their singleton meet a 1-split strictly before the cap.

For a target sharing that first leaf, equality of its capped full
pair meet with the first leaf is EQUIVALENT to target full pair-type
agreement all the way to that leaf's index. The current fused I3
only guarantees agreement at the image of the preceding diary cut,
and must not silently be extended through skipped target levels.

These theorems isolate the exact remaining capped-case obligation
without postulating an invalid global type-meet transfer.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

variable {H : Ordered3Graph Nat}

/-- A source diary full pair meet capped at min(a,c) forces the
first leaf coordinates to be identical. No V/E coherence axioms
are needed here; S1 and the full two-meet decomposition suffice. -/
theorem capped_leaf_pairs_first_eq
    (D : RoleDiary H) (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hc : IsLeaf H c)
    (hcap : H.twoMeetLevel a b c d = min a c) :
    a = c := by
  by_contra hneq
  have hone : IsOneSplit H (H.oneMeetLevel a c) :=
    D.singleton_meets a c ha hc hneq
  have htwoLe : H.twoMeetLevel a b c d ≤ H.oneMeetLevel a c := by
    rw [H.twoMeetLevel_eq_min a b c d hab hcd]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have honeEq : H.oneMeetLevel a c = min a c := by
    have hle := H.oneMeetLevel_le_min a c
    omega
  rcases le_total a c with hac | hca
  · have heq : H.oneMeetLevel a c = a := by
      simpa [min_eq_left hac] using honeEq
    have hsplit : IsOneSplit H a := by
      simpa only [heq] using hone
    exact ha.2.1 hsplit.2.1
  · have heq : H.oneMeetLevel a c = c := by
      simpa [min_eq_right hca] using honeEq
    have hsplit : IsOneSplit H c := by
      simpa only [heq] using hone
    exact hc.2.1 hsplit.2.1

end RoleDiary
end DiaryLeafPriority

namespace Ordered3Graph

/-- At a common first vertex, the capped full target pair meet
equals that vertex iff the actual pair types agree at its index.
This is the precise capped-case obligation in the pre-embedding
proof, independent of the source diary. -/
theorem capped_twoMeetLevel_eq_first_iff
    (K : Ordered3Graph Nat) (a b d : Nat) :
    K.twoMeetLevel a b a d = a ↔
      K.SameTwoTypeBelow a a b a d := by
  constructor
  · intro heq
    simpa only [heq] using K.twoMeetLevel_agree a b a d
  · intro h
    have hlow : a ≤ K.twoMeetLevel a b a d :=
      (K.twoMeetLevel_ge_iff_sameTwoTypeBelow
        a a b a d (by omega) (by omega)).mpr h
    have htop : K.twoMeetLevel a b a d ≤ a := by
      have h := K.twoMeetLevel_le_min a b a d
      simpa only [min_self] using h
    exact Nat.le_antisymm htop hlow

end Ordered3Graph
end ThreeUniformDiaries
