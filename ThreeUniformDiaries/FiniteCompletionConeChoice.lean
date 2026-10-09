import ThreeUniformDiaries.ProtectedConeTruncations
import ThreeUniformDiaries.ZeroExtendLevels

/-!
# The local selection rule in finite strong-subtree completion

For a child cone t and the next selected level L, make a choice that
both fills that cone and protects all prescribed nodes of E:

* If E has a descendant x of t at or above L, select x|_L.
  Meet-closure and the lack of intervening E-levels ensure this
  choice is independent of x.
* Otherwise use the canonical zero extension of t to level L.

Thus every child cone receives exactly one candidate, preserving
all later prescribed nodes. The separate uniqueness and
different-child meet lemmas will assemble these choices into layers.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- A protected completion choice for an immediate successor cone. -/
noncomputable def completionChoice
    (E : Set CoordNode) (t : CoordNode) (L : Nat)
    (htL : level t ≤ L) : CoordNode := by
  classical
  by_cases h : ∃ x ∈ E, t ≤ x ∧ L ≤ level x
  · exact protectedGuide E t L h
  · exact zeroExtendTo t L htL

/-- Every chosen candidate is on the requested level. -/
theorem completionChoice_level
    (E : Set CoordNode) (t : CoordNode) (L : Nat)
    (htL : level t ≤ L) :
    level (completionChoice E t L htL) = L := by
  classical
  unfold completionChoice
  split
  · exact protectedGuide_level E t L ‹_›
  · exact level_zeroExtendTo t L htL

/-- The chosen node always belongs to the required child cone. -/
theorem completionChoice_extends
    (E : Set CoordNode) (t : CoordNode) (L : Nat)
    (htL : level t ≤ L) :
    t ≤ completionChoice E t L htL := by
  classical
  unfold completionChoice
  split
  · exact protectedGuide_extends E t L htL ‹_›
  · exact le_zeroExtendTo t L htL

/-- Every prescribed upper node extending t also extends the chosen
candidate. The look-ahead condition prevents the finite completion
from accidentally deleting a later E-node. -/
theorem completionChoice_below_prescribed
    (E : Set CoordNode) (hE : MeetClosed E)
    (l L : Nat) (hgap : AvoidsOpenLevelGap E l L)
    (t : CoordNode) (hlt : l < level t)
    (htL : level t ≤ L)
    (x : CoordNode) (hx : x ∈ E)
    (htx : t ≤ x) (hLx : L ≤ level x) :
    completionChoice E t L htL ≤ x := by
  classical
  have hex : ∃ y ∈ E, t ≤ y ∧ L ≤ level y :=
    ⟨x, hx, htx, hLx⟩
  change (if h : ∃ y ∈ E, t ≤ y ∧ L ≤ level y then
        protectedGuide E t L h
      else zeroExtendTo t L htL) ≤ x
  rw [dif_pos hex]
  exact protectedGuide_below E hE l L hgap
    t x hlt hx htx hLx hex

/-- The chosen candidate is precisely the L-ancestor of every
prescribed node in its cone, whenever one exists. -/
theorem completionChoice_eq_truncate
    (E : Set CoordNode) (hE : MeetClosed E)
    (l L : Nat) (hgap : AvoidsOpenLevelGap E l L)
    (t : CoordNode) (hlt : l < level t)
    (htL : level t ≤ L)
    (x : CoordNode) (hx : x ∈ E)
    (htx : t ≤ x) (hLx : L ≤ level x) :
    completionChoice E t L htL = truncate x L := by
  have hbelow := completionChoice_below_prescribed E hE l L
    hgap t hlt htL x hx htx hLx
  have hprefix := hbelow.2
  rw [completionChoice_level E t L htL] at hprefix
  exact hprefix.symm

/-- In particular an E-node already at L is left *unchanged* by the
completion choice, whenever it extends the selected child t. -/
theorem completionChoice_eq_selected
    (E : Set CoordNode) (hE : MeetClosed E)
    (l L : Nat) (hgap : AvoidsOpenLevelGap E l L)
    (t : CoordNode) (hlt : l < level t)
    (htL : level t ≤ L)
    (x : CoordNode) (hx : x ∈ E)
    (htx : t ≤ x) (hxL : level x = L) :
    completionChoice E t L htL = x := by
  have h := completionChoice_eq_truncate E hE l L
    hgap t hlt htL x hx htx (by omega)
  rw [← hxL, truncate_self] at h
  exact h

end CoordNode
end ThreeUniformDiaries
