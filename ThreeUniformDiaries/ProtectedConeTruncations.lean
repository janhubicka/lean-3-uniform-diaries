import ThreeUniformDiaries.MeetClosedGapRigidity

/-!
# Protecting prescribed higher nodes in a finite strong-tree completion

A completion of a meet-closed picture E must retain *all* its nodes.
When filling the child cone above a selected node p on level l and
moving to the next selected level L, we must look ahead: if E has
any descendant x in that cone on a level >= L, choose x|_L.

The key point is uniqueness: all such descendants have the same
restriction to L. Otherwise their meet would belong to E on a
forbidden level strictly between l and L.

This is the "protected choice" invariant for the forthcoming finite
strong-subtree completion. It is independent of the hypergraph type
coordinates.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The l-L gap of a meet-closed picture has no occupied intervening
levels. We allow arbitrary nodes outside the interval. -/
def AvoidsOpenLevelGap (S : Set CoordNode) (l L : Nat) : Prop :=
  ∀ x ∈ S, level x ≤ l ∨ L ≤ level x

/-- Two prescribed descendants of the same cone above l must have
identical ancestors at the next selected level L. -/
theorem protectedCone_same_truncation
    (S : Set CoordNode) (hS : MeetClosed S)
    (l L : Nat)
    (hgap : AvoidsOpenLevelGap S l L)
    (t x y : CoordNode)
    (hlt : l < level t)
    (htx : t ≤ x) (hty : t ≤ y)
    (hx : x ∈ S) (hy : y ∈ S)
    (hLx : L ≤ level x) (hLy : L ≤ level y) :
    truncate x L = truncate y L := by
  let q := meet x y
  have hqS : q ∈ S := hS hx hy
  have htq : t ≤ q := le_meet htx hty
  have hLq : L ≤ level q := by
    rcases hgap q hqS with hlo | hhi
    · have htlow : level t ≤ level q := level_le_of_le htq
      omega
    · exact hhi
  have hqx : q ≤ x := meet_le_left ⟨t, htx, hty⟩
  have hqy : q ≤ y := meet_le_right ⟨t, htx, hty⟩
  calc
    truncate x L =
        truncate (truncate x (level q)) L :=
          (truncate_truncate x hLq).symm
    _ = truncate q L := by rw [hqx.2]
    _ = truncate (truncate y (level q)) L := by rw [hqy.2]
    _ = truncate y L := truncate_truncate y hLq

/-- The last assertion specialised when the first selected node lies
already at level L: it must be the ancestor of every later prescribed
node passing through the same child cone. -/
theorem protectedCone_existing_eq
    (S : Set CoordNode) (hS : MeetClosed S)
    (l L : Nat) (hgap : AvoidsOpenLevelGap S l L)
    (t x y : CoordNode)
    (hlt : l < level t)
    (htx : t ≤ x) (hty : t ≤ y)
    (hx : x ∈ S) (hy : y ∈ S)
    (hlevel : level x = L) (hLy : L ≤ level y) :
    x = truncate y L := by
  have h := protectedCone_same_truncation S hS l L hgap
    t x y hlt htx hty hx hy (by omega) hLy
  have hxself : truncate x L = x := by
    rw [← hlevel]
    exact truncate_self x
  exact hxself.symm.trans h

/-- The distinguished ancestor at level L can be read from any
prescribed higher descendant; all choices agree. -/
noncomputable def protectedGuide
    (S : Set CoordNode) (t : CoordNode) (L : Nat)
    (hex : ∃ x ∈ S, t ≤ x ∧ L ≤ level x) : CoordNode :=
  truncate (Classical.choose hex) L

theorem protectedGuide_level
    (S : Set CoordNode) (t : CoordNode) (L : Nat)
    (hex : ∃ x ∈ S, t ≤ x ∧ L ≤ level x) :
    level (protectedGuide S t L hex) = L :=
  level_truncate _ _

/-- The protected guide belongs to the prescribed child's cone,
provided that child is no higher than the selected target level. -/
theorem protectedGuide_extends
    (S : Set CoordNode) (t : CoordNode) (L : Nat)
    (htL : level t ≤ L)
    (hex : ∃ x ∈ S, t ≤ x ∧ L ≤ level x) :
    t ≤ protectedGuide S t L hex := by
  let x := Classical.choose hex
  have hx : t ≤ x := (Classical.choose_spec hex).2.1
  refine ⟨by simp [protectedGuide, htL], ?_⟩
  change truncate (truncate x L) (level t) = t
  calc
    truncate (truncate x L) (level t) = truncate x (level t) :=
      truncate_truncate x htL
    _ = t := hx.2

/-- Every prescribed higher node in this cone extends the *same*
chosen guide at the next selected level. -/
theorem protectedGuide_below
    (S : Set CoordNode) (hS : MeetClosed S)
    (l L : Nat) (hgap : AvoidsOpenLevelGap S l L)
    (t y : CoordNode) (hlt : l < level t)
    (hy : y ∈ S) (hty : t ≤ y) (hLy : L ≤ level y)
    (hex : ∃ x ∈ S, t ≤ x ∧ L ≤ level x) :
    protectedGuide S t L hex ≤ y := by
  let x := Classical.choose hex
  have hx : x ∈ S := (Classical.choose_spec hex).1
  have htx : t ≤ x := (Classical.choose_spec hex).2.1
  have hLx : L ≤ level x := (Classical.choose_spec hex).2.2
  have heq : protectedGuide S t L hex = truncate y L := by
    exact protectedCone_same_truncation S hS l L hgap t x y
      hlt htx hty hx hy hLx hLy
  rw [heq]
  exact truncate_le y hLy

end CoordNode
end ThreeUniformDiaries
