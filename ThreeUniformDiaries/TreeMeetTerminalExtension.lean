import ThreeUniformDiaries.CoordinateTree

/-!
# Adding a terminal extension to a meet-closed tree picture

A meet-closed subset of a levelled tree stays meet-closed when a
single new terminal node is added above a member, provided all
old nodes lie at or below that member's level. This justifies the
terminal auxiliary-type node added to E2^- in the finite strong-tree
encoder. The lemma assumes all relevant pairs have a common
predecessor, as CoordNode is a forest of three coordinate trees.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Meets are symmetric whenever a common predecessor exists. -/
theorem meet_comm_of_common
    (x y : CoordNode)
    (hc : ∃ c : CoordNode, c ≤ x ∧ c ≤ y) :
    meet x y = meet y x := by
  have hrev : ∃ c : CoordNode, c ≤ y ∧ c ≤ x := by
    rcases hc with ⟨c, hcx, hcy⟩
    exact ⟨c, hcy, hcx⟩
  apply le_antisymm
  · exact le_meet (meet_le_right hc) (meet_le_left hc)
  · exact le_meet (meet_le_right hrev) (meet_le_left hrev)

/-- A node meets itself in itself. -/
theorem meet_self (x : CoordNode) : meet x x = x := by
  let hc : ∃ c : CoordNode, c ≤ x ∧ c ≤ x :=
    ⟨x, le_refl x, le_refl x⟩
  exact le_antisymm (meet_le_left hc)
    (le_meet (le_refl x) (le_refl x))

/-- Extending p to z does not change its meet with any old x whose
level is no larger than the level of p. -/
theorem meet_extension_left
    (p z x : CoordNode)
    (hpz : p ≤ z)
    (hxp : level x ≤ level p)
    (hc : ∃ c : CoordNode, c ≤ p ∧ c ≤ x) :
    meet z x = meet p x := by
  have hczx : ∃ c : CoordNode, c ≤ z ∧ c ≤ x := by
    rcases hc with ⟨c, hcp, hcx⟩
    exact ⟨c, hcp.trans hpz, hcx⟩
  let q := meet z x
  have hqz : q ≤ z := meet_le_left hczx
  have hqx : q ≤ x := meet_le_right hczx
  have hql : level q ≤ level p :=
    (level_le_of_le hqx).trans hxp
  have hqp : q ≤ p := by
    refine ⟨hql, ?_⟩
    calc
      truncate p (level q) =
          truncate (truncate z (level p)) (level q) := by
            rw [hpz.2]
      _ = truncate z (level q) := truncate_truncate z hql
      _ = q := hqz.2
  apply le_antisymm
  · exact le_meet hqp hqx
  · exact le_meet (le_trans (meet_le_left hc) hpz)
      (meet_le_right hc)

/-- The same terminal-extension identity in the other argument. -/
theorem meet_extension_right
    (x p z : CoordNode)
    (hpz : p ≤ z)
    (hxp : level x ≤ level p)
    (hc : ∃ c : CoordNode, c ≤ p ∧ c ≤ x) :
    meet x z = meet x p := by
  have hcxz : ∃ c : CoordNode, c ≤ x ∧ c ≤ z := by
    rcases hc with ⟨c, hcp, hcx⟩
    exact ⟨c, hcx, hcp.trans hpz⟩
  calc
    meet x z = meet z x := meet_comm_of_common x z hcxz
    _ = meet p x := meet_extension_left p z x hpz hxp hc
    _ = meet x p := meet_comm_of_common p x hc

/-- Meet-closure in one coordinate tree. -/
def MeetClosed (S : Set CoordNode) : Prop :=
  ∀ ⦃x y : CoordNode⦄, x ∈ S → y ∈ S → meet x y ∈ S

/-- Adding a single node above the last selected level leaves the
old meet-closed picture meet-closed. -/
theorem meetClosed_insertAbove
    (S : Set CoordNode) (hS : MeetClosed S)
    (p z : CoordNode) (hp : p ∈ S) (hpz : p ≤ z)
    (hmax : ∀ x ∈ S, level x ≤ level p)
    (hcommon : ∀ x ∈ S, ∃ c : CoordNode, c ≤ p ∧ c ≤ x) :
    MeetClosed (Set.insert z S) := by
  intro x y hx hy
  rcases hx with hx | hx
  · subst x
    rcases hy with hy | hy
    · subst y
      left
      exact meet_self z
    · right
      rw [meet_extension_left p z y hpz (hmax y hy) (hcommon y hy)]
      exact hS hp hy
  · rcases hy with hy | hy
    · subst y
      right
      rw [meet_extension_right x p z hpz (hmax x hx) (hcommon x hx)]
      exact hS hx hp
    · right
      exact hS hx hy

end CoordNode
end ThreeUniformDiaries
