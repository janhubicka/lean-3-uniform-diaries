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

/-- For distinct second leaves, a capped source full pair meet
forces their singleton meet to be a 1-split STRICTLY after the
common first leaf. It cannot coincide with that leaf because
a leaf cannot also have the one-split marker role. -/
theorem capped_leaf_pairs_second_meet_later
    (D : RoleDiary H) (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hbd : b ≠ d)
    (hcap : H.twoMeetLevel a b c d = min a c) :
    a < H.oneMeetLevel b d := by
  have hac : a = c :=
    D.capped_leaf_pairs_first_eq a b c d hab hcd ha hc hcap
  subst c
  have hfullEq : H.twoMeetLevel a b a d = a := by
    simpa only [min_self] using hcap
  have hle : H.twoMeetLevel a b a d ≤ H.oneMeetLevel b d := by
    rw [H.twoMeetLevel_eq_min a b a d hab hcd]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hsplit : IsOneSplit H (H.oneMeetLevel b d) :=
    D.singleton_meets b d hb hd hbd
  have hneq : H.oneMeetLevel b d ≠ a := by
    intro heq
    have hs : IsOneSplit H a := by
      simpa only [heq] using hsplit
    exact ha.2.1 hs.2.1
  omega

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

/-- A late singleton meet of the SECOND coordinates is enough
to force the full capped pair meet of (a,b) and (a,d) to be a.
This is the key repair for the capped case: the auxiliary
incidences edge(x,a,b) and edge(x,a,d) are already bits of the
singleton types of b and d, evaluated at the earlier pair (x,a).
No independent auxiliary-gap preservation is necessary. -/
theorem capped_twoMeetLevel_eq_first_of_late_singleton
    (K : Ordered3Graph Nat) (a b d : Nat)
    (hab : a < b) (had : a < d)
    (hlate : a < K.oneMeetLevel b d) :
    K.twoMeetLevel a b a d = a := by
  have hSameOne : K.SameOneTypeBelow (a+1) b d := by
    intro x y hxy hy
    exact K.oneMeetLevel_agree b d hxy (by omega)
  apply (K.capped_twoMeetLevel_eq_first_iff a b d).2
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy hy
    rfl
  · intro x y hxy hy
    exact hSameOne hxy (by omega)
  · intro x hx
    exact hSameOne (a := x) (b := a) hx (by omega)

end Ordered3Graph

namespace DiaryLeafPriority
namespace RoleDiary

/-- A source capped leaf-pair meet is preserved by ANY strictly
increasing target embedding as soon as the target singleton
meet of the two second leaves lies after the common first leaf.
The source S1 rule first proves the common leaf identity, and
the target singleton-type lemma supplies all auxiliary bits. -/
theorem capped_leaf_pair_target_of_late_singleton
    {H K : Ordered3Graph Nat}
    (D : RoleDiary H) (φ : Ordered3Graph.Embedding H K)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hc : IsLeaf H c)
    (hcap : H.twoMeetLevel a b c d = min a c)
    (hlate : φ a < K.oneMeetLevel (φ b) (φ d)) :
    K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) = φ a := by
  have hac : a = c :=
    D.capped_leaf_pairs_first_eq a b c d hab hcd ha hc hcap
  subst c
  exact K.capped_twoMeetLevel_eq_first_of_late_singleton
    (φ a) (φ b) (φ d)
    (φ.strictMono hab) (φ.strictMono hcd) hlate

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
