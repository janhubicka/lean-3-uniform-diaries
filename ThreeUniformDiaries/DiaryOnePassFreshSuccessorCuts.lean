import ThreeUniformDiaries.DiaryOnePassRoleCoverage

/-!
# Successor-cut identities at actual inserted one-pass split levels

The concrete raw one-pass target now satisfies the complete E1--E5
permitted-edge classification and all marker roles, without assuming
V1/V2/V3 or S1/S2 of the target. In particular:

* a target 1-split m can only occur in the middle position of an edge
  with first coordinate 0;
* a target 2-split m NEVER occurs in the middle position of an edge.

We derive the exact singleton and full pair-type successor-cut
formulas from E alone, and specialize them to ACTUAL inserted events
with their genuine target split roles.

These are local geometrical formulas for the next cut after one
event. They do not claim the global original-cut induction or diary
completion.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

variable {H : Ordered3Graph Nat}

/-- Under the ACTUAL target E axiom, a 1-split can be the middle
vertex of an edge only when its first vertex is 0. -/
theorem onePassRawTarget_oneSplit_no_nonzero_middle
    (P : RolePrediary H) (m z u : Nat)
    (hm : IsOneSplit (onePassRawTarget H) m) (hz : z ≠ 0) :
    ¬ (onePassRawTarget H).edge z m u := by
  have hNotLeaf : ¬ IsLeaf (onePassRawTarget H) m := by
    intro h
    exact h.2.1 hm.2.1
  intro he
  rcases onePassRawTarget_permitted_edge P z m u he with
      hRole | hSplit | hTwo | hDevlin | hNormal
  · exact hz hRole.1
  · exact hz hSplit.1
  · exact hNotLeaf hTwo.2.1
  · exact hNotLeaf hDevlin.2.1
  · exact hNotLeaf hNormal.2.1

/-- Under the ACTUAL target E axiom, no increasing triple has
a 2-split in its middle position. -/
theorem onePassRawTarget_twoSplit_no_middle
    (P : RolePrediary H) (m z u : Nat)
    (hm : IsTwoSplit (onePassRawTarget H) m) :
    ¬ (onePassRawTarget H).edge z m u := by
  have hNotLeaf : ¬ IsLeaf (onePassRawTarget H) m := by
    intro h
    exact h.2.2 hm.2.2
  have hNotOne : ¬ IsOneSplit (onePassRawTarget H) m := by
    intro h
    exact hm.2.1 h.2.1
  intro he
  rcases onePassRawTarget_permitted_edge P z m u he with
      hRole | hSplit | hTwo | hDevlin | hNormal
  · have h3 := hm.1
    rcases hRole.2.1 with h | h <;> omega
  · exact hNotOne hSplit.2.1
  · exact hNotLeaf hTwo.2.1
  · exact hNotLeaf hDevlin.2.1
  · exact hNotLeaf hNormal.2.1

/-- Advancing the singleton cut through a target 1-split
adds exactly its (0,m,u) bit, and no other middle-column test. -/
theorem onePassRawTarget_oneSplit_sameOneType_succ_iff
    (P : RolePrediary H) (m u v : Nat)
    (hm : IsOneSplit (onePassRawTarget H) m) :
    (onePassRawTarget H).SameOneTypeBelow (m + 1) u v ↔
      (onePassRawTarget H).SameOneTypeBelow m u v ∧
      ((onePassRawTarget H).edge 0 m u ↔
       (onePassRawTarget H).edge 0 m v) := by
  rw [(onePassRawTarget H).sameOneTypeBelow_succ_iff m u v]
  constructor
  · rintro ⟨hBefore,hColumn⟩
    have h0 : 0 < m := by have h3 := hm.1; omega
    exact ⟨hBefore,hColumn 0 h0⟩
  · rintro ⟨hBefore,hBit⟩
    constructor
    · exact hBefore
    · intro z hz
      by_cases hz0 : z = 0
      · subst z
        exact hBit
      · exact iff_of_false
          (onePassRawTarget_oneSplit_no_nonzero_middle P m z u hm hz0)
          (onePassRawTarget_oneSplit_no_nonzero_middle P m z v hm hz0)

/-- Advancing the singleton cut through a target 2-split changes
no singleton coordinate, including for original leaf images. -/
theorem onePassRawTarget_twoSplit_sameOneType_succ_iff
    (P : RolePrediary H) (m u v : Nat)
    (hm : IsTwoSplit (onePassRawTarget H) m) :
    (onePassRawTarget H).SameOneTypeBelow (m + 1) u v ↔
      (onePassRawTarget H).SameOneTypeBelow m u v := by
  rw [(onePassRawTarget H).sameOneTypeBelow_succ_iff m u v]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    intro z hz
    exact iff_of_false
      (onePassRawTarget_twoSplit_no_middle P m z u hm)
      (onePassRawTarget_twoSplit_no_middle P m z v hm)

/-- Advancing the FULL pair-type cut through a target 2-split
changes neither singleton component; only its new auxiliary
edge (m,a,b) bit is added. This uses target E alone. -/
theorem onePassRawTarget_twoSplit_sameTwoType_succ_iff
    (P : RolePrediary H) (m a b c d : Nat)
    (hm : IsTwoSplit (onePassRawTarget H) m) :
    (onePassRawTarget H).SameTwoTypeBelow (m + 1) a b c d ↔
      (onePassRawTarget H).SameTwoTypeBelow m a b c d ∧
      ((onePassRawTarget H).edge m a b ↔
       (onePassRawTarget H).edge m c d) := by
  constructor
  · intro h
    have hAux := h.2.2
    constructor
    · refine ⟨?_, ?_, ?_⟩
      · intro x y hxy hy
        exact h.1 hxy (by omega)
      · intro x y hxy hy
        exact h.2.1 hxy (by omega)
      · intro x hx
        exact hAux (a := x) (by omega)
    · exact hAux (a := m) (by omega)
  · rintro ⟨h,hBit⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy hy
      by_cases hyold : y < m
      · exact h.1 hxy hyold
      · have hym : y = m := by omega
        subst y
        exact iff_of_false
          (onePassRawTarget_twoSplit_no_middle P m x a hm)
          (onePassRawTarget_twoSplit_no_middle P m x c hm)
    · intro x y hxy hy
      by_cases hyold : y < m
      · exact h.2.1 hxy hyold
      · have hym : y = m := by omega
        subst y
        exact iff_of_false
          (onePassRawTarget_twoSplit_no_middle P m x b hm)
          (onePassRawTarget_twoSplit_no_middle P m x d hm)
    · intro x hx
      by_cases hxold : x < m
      · exact h.2.2 hxold
      · have hxm : x = m := by omega
        subst x
        exact hBit

/-- The actual singleton event satisfies the exact successor
singleton-type formula at its target index. -/
theorem onePassRawTarget_freshOne_event_nextCut
    (P : RolePrediary H) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : OneGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.singleton m g)
    (u v : Nat) :
    (onePassRawTarget H).SameOneTypeBelow
        (onePassEventPosition H m i + 1) u v ↔
      (onePassRawTarget H).SameOneTypeBelow
        (onePassEventPosition H m i) u v ∧
      ((onePassRawTarget H).edge 0
          (onePassEventPosition H m i) u ↔
       (onePassRawTarget H).edge 0
          (onePassEventPosition H m i) v) := by
  exact onePassRawTarget_oneSplit_sameOneType_succ_iff P
    (onePassEventPosition H m i) u v
    (onePassRawTarget_fresh_oneSplit H m i g hget)

/-- The actual pair event adds no singleton test at its own
middle-coordinate cut. -/
theorem onePassRawTarget_freshTwo_event_nextOneCut
    (P : RolePrediary H) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : TwoGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.pair m g)
    (u v : Nat) :
    (onePassRawTarget H).SameOneTypeBelow
        (onePassEventPosition H m i + 1) u v ↔
      (onePassRawTarget H).SameOneTypeBelow
        (onePassEventPosition H m i) u v := by
  exact onePassRawTarget_twoSplit_sameOneType_succ_iff P
    (onePassEventPosition H m i) u v
    (onePassRawTarget_fresh_twoSplit H m i g hget)

/-- The actual pair event's full two-type successor-cut test
is EXACTLY its selected original-pair incidence bit. -/
theorem onePassRawTarget_freshTwo_event_nextTwoCut
    (P : RolePrediary H) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : TwoGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.pair m g)
    (a b c d : Nat) :
    (onePassRawTarget H).SameTwoTypeBelow
        (onePassEventPosition H m i + 1) a b c d ↔
      (onePassRawTarget H).SameTwoTypeBelow
        (onePassEventPosition H m i) a b c d ∧
      ((onePassRawTarget H).edge
          (onePassEventPosition H m i) a b ↔
       (onePassRawTarget H).edge
          (onePassEventPosition H m i) c d) := by
  exact onePassRawTarget_twoSplit_sameTwoType_succ_iff P
    (onePassEventPosition H m i) a b c d
    (onePassRawTarget_fresh_twoSplit H m i g hget)

end DiaryLeafPriority
end ThreeUniformDiaries
