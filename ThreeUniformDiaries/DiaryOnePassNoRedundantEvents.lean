import ThreeUniformDiaries.DiaryFullRoleDefinition

/-!
# No redundant one-pass type-refinement events in an existing diary

This is a formal audit of the "identity on diaries" claim in the
one-pass pre-diary completion proof. The original diary conditions
S1/S2 rule out exactly the parent-child patterns which would
otherwise create new events before old leaf or wrong-role split
levels.

There are four independent facts:
1. a terminal leaf and a later leaf cannot share the old parent
   singleton type at the terminal cut (S1);
2. two later leaves whose old singleton m-types agree cannot
   acquire different (m+1)-types at an old leaf m (S1);
3. a terminal ordered leaf pair and a normal pair cannot share
   the old full pair parent (already excluded by S1);
4. two normal pair children cannot branch at any original level
   m >= 3 not marked as a 2-split (S2).

These statements concern the ORIGINAL diary only; they do not
assume, define or prove the complete one-pass construction.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

variable {H : Ordered3Graph Nat} (D : RoleDiary H)

/-- The terminal leaf m and any strictly later leaf cannot
have the same original singleton type over cut m. -/
theorem terminal_leaf_not_normal_singleton_parent
    (D : RoleDiary H)
    (m u : Nat) (hm : IsLeaf H m) (hu : IsLeaf H u)
    (hmu : m < u) :
    ¬ H.SameOneTypeBelow m m u := by
  classical
  intro hparent
  have hbound : m ≤ min m u := by omega
  have hLower : m ≤ H.oneMeetLevel m u :=
    Nat.le_findGreatest hbound hparent
  have hUpper : H.oneMeetLevel m u ≤ m := by
    have hmax := H.oneMeetLevel_le_min m u
    omega
  have hMeet : H.oneMeetLevel m u = m := by omega
  have hRole := D.singleton_meets m u hm hu (by omega)
  have hOne : IsOneSplit H m := by
    simpa only [hMeet] using hRole
  exact hm.2.1 hOne.2.1

/-- Two normal children in one old singleton parent cannot
be distinguished at a level whose source role is leaf. -/
theorem leaf_no_normal_singleton_refinement
    (D : RoleDiary H)
    (m u v : Nat) (hm : IsLeaf H m)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m < u) (hmv : m < v)
    (hparent : H.SameOneTypeBelow m u v) :
    H.SameOneTypeBelow (m + 1) u v := by
  classical
  by_cases huv : u = v
  · subst v
    intro a b hab hb
    rfl
  · by_contra hNext
    have hbound : m ≤ min u v := by omega
    have hLower : m ≤ H.oneMeetLevel u v :=
      Nat.le_findGreatest hbound hparent
    have hUpper : H.oneMeetLevel u v ≤ m := by
      by_contra hgt
      have hs : H.SameOneTypeBelow (m + 1) u v := by
        intro a b hab hb
        exact (H.oneMeetLevel_agree u v) hab (by omega)
      exact hNext hs
    have hMeet : H.oneMeetLevel u v = m := by omega
    have hRole := D.singleton_meets u v hu hv huv
    have hOne : IsOneSplit H m := by
      simpa only [hMeet] using hRole
    exact hm.2.1 hOne.2.1

/-- A terminal pair (m,u) cannot belong to the same
old full pair parent as a normal pair (a,b), a>m:
their first singleton components are already different. -/
theorem terminal_pair_not_normal_pair_parent
    (D : RoleDiary H)
    (m u a b : Nat)
    (hm : IsLeaf H m) (ha : IsLeaf H a)
    (hma : m < a) :
    ¬ H.SameTwoTypeBelow m m u a b := by
  intro hpair
  exact D.terminal_leaf_not_normal_singleton_parent
    m a hm ha hma hpair.1

/-- Two normal pair type children sharing the old parent
cannot branch at any original level m>=3 that is NOT
a 2-split. Otherwise their exact full meet would be m,
violating S2 (neither marker 1, common leaf cap, nor a 2-split). -/
theorem no_normal_pair_refinement_without_twoSplit
    (D : RoleDiary H)
    (m a b c d : Nat) (hm3 : 3 ≤ m)
    (hNotTwo : ¬ IsTwoSplit H m)
    (hab : a < b) (hcd : c < d)
    (hma : m < a) (hmc : m < c)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hparent : H.SameTwoTypeBelow m a b c d) :
    H.SameTwoTypeBelow (m + 1) a b c d := by
  classical
  by_contra hNext
  have hbound : m ≤ min a c := by omega
  have hLower : m ≤ H.twoMeetLevel a b c d :=
    Nat.le_findGreatest hbound hparent
  have hUpper : H.twoMeetLevel a b c d ≤ m := by
    by_contra hgt
    have hs : H.SameTwoTypeBelow (m+1) a b c d := by
      have hall := H.twoMeetLevel_agree a b c d
      refine ⟨?_, ?_, ?_⟩
      · intro x y hxy hy
        exact hall.1 hxy (by omega)
      · intro x y hxy hy
        exact hall.2.1 hxy (by omega)
      · intro x hx
        exact hall.2.2 (by omega)
    exact hNext hs
  have hMeet : H.twoMeetLevel a b c d = m := by omega
  rcases D.pair_meets a b c d hab hcd ha hb hc hd with
      hcap | hone | htwo
  · have hmin : m < min a c := lt_min hma hmc
    omega
  · omega
  · apply hNotTwo
    simpa only [hMeet] using htwo

/-- Application to an old leaf level (both new event
families would have been redundant in a complete diary). -/
theorem leaf_no_normal_pair_refinement
    (D : RoleDiary H)
    (m a b c d : Nat) (hm : IsLeaf H m)
    (hab : a < b) (hcd : c < d)
    (hma : m < a) (hmc : m < c)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hparent : H.SameTwoTypeBelow m a b c d) :
    H.SameTwoTypeBelow (m+1) a b c d := by
  apply D.no_normal_pair_refinement_without_twoSplit
    m a b c d hm.1 ?_ hab hcd hma hmc ha hb hc hd hparent
  intro hTwo
  exact hm.2.2 hTwo.2.2

/-- Application to an old 1-split: there cannot be a
new 2-split event in its block when the source is a diary. -/
theorem oneSplit_no_normal_pair_refinement
    (D : RoleDiary H)
    (m a b c d : Nat) (hm : IsOneSplit H m)
    (hab : a < b) (hcd : c < d)
    (hma : m < a) (hmc : m < c)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hparent : H.SameTwoTypeBelow m a b c d) :
    H.SameTwoTypeBelow (m+1) a b c d := by
  apply D.no_normal_pair_refinement_without_twoSplit
    m a b c d hm.1 ?_ hab hcd hma hmc ha hb hc hd hparent
  intro hTwo
  exact hTwo.2.1 hm.2.1

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
