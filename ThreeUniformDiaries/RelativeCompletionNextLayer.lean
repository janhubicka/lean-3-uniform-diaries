import ThreeUniformDiaries.RelativeProtectedConeChoice

/-!
# Saturating one selected relative level INSIDE a strong coordinate picture

The ambient finite completion inserts one representative in every
immediate cone. A strong coordinate picture U has its own successor
cones, separated by selected ambient levels f i. We replace ambient
children by the corresponding retained relative children.

The protected choice is already verified to stay inside U and to
retain all future prescribed E-nodes. This file assembles a finite
next layer from one choice per retained relative cone, including the
correct relative strong-branching uniqueness.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- A successor cone in U from relative level i to level i+1. -/
structure RelativeGapChild
    (U P : Set CoordNode) (f : Nat → Nat) (i : Nat) where
  parent : CoordNode
  parent_mem : parent ∈ P
  parent_level : level parent = f i
  child : CoordNode
  child_mem : child ∈ U
  child_level : level child = f (i + 1)
  parent_le_child : parent ≤ child

namespace RelativeGapChild

/-- Canonical protected representative on a later chosen relative
level, with future E-nodes taking priority. -/
noncomputable def chosen
    {U P : Set CoordNode} {f : Nat → Nat} {i : Nat}
    (g : RelativeGapChild U P f i)
    {root : CoordNode} (hU : InfiniteStrongPicture U f root)
    (E : Set CoordNode) (L : Nat) (hL : i + 1 ≤ L) : CoordNode :=
  relativeProtectedChoice hU E i L hL
    g.child g.child_mem g.child_level

theorem chosen_level
    {U P : Set CoordNode} {f : Nat → Nat} {i : Nat}
    (g : RelativeGapChild U P f i)
    {root : CoordNode} (hU : InfiniteStrongPicture U f root)
    (E : Set CoordNode) (L : Nat) (hL : i + 1 ≤ L) :
    level (g.chosen hU E L hL) = f L :=
  relativeProtectedChoice_level hU E i L hL
    g.child g.child_mem g.child_level

theorem chosen_mem
    {U P : Set CoordNode} {f : Nat → Nat} {i : Nat}
    (g : RelativeGapChild U P f i)
    {root : CoordNode} (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f) (hroot : level root = f 0)
    (E : Set CoordNode) (hEU : E ⊆ U)
    (L : Nat) (hL : i + 1 ≤ L) :
    g.chosen hU E L hL ∈ U :=
  relativeProtectedChoice_mem hU hf hroot E hEU
    i L hL g.child g.child_mem g.child_level

theorem child_le_chosen
    {U P : Set CoordNode} {f : Nat → Nat} {i : Nat}
    (g : RelativeGapChild U P f i)
    {root : CoordNode} (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f) (E : Set CoordNode)
    (L : Nat) (hL : i + 1 ≤ L) :
    g.child ≤ g.chosen hU E L hL :=
  relativeProtectedChoice_extends hU hf E i L hL
    g.child g.child_mem g.child_level

theorem parent_le_chosen
    {U P : Set CoordNode} {f : Nat → Nat} {i : Nat}
    (g : RelativeGapChild U P f i)
    {root : CoordNode} (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f) (E : Set CoordNode)
    (L : Nat) (hL : i + 1 ≤ L) :
    g.parent ≤ g.chosen hU E L hL :=
  le_trans g.parent_le_child (g.child_le_chosen hU hf E L hL)

end RelativeGapChild

/-- All protected representatives, exactly one for each retained
relative child cone of the previous parent layer. -/
noncomputable def relativeNextLayer
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (E P : Set CoordNode) (i L : Nat) (hL : i + 1 ≤ L) :
    Set CoordNode :=
  Set.range (fun g : RelativeGapChild U P f i =>
    g.chosen hU E L hL)

/-- The next relative layer lies on one prescribed ambient level. -/
theorem relativeNextLayer_level
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (E P : Set CoordNode) (i L : Nat) (hL : i + 1 ≤ L)
    (z : CoordNode) (hz : z ∈ relativeNextLayer hU E P i L hL) :
    level z = f L := by
  rcases hz with ⟨g, rfl⟩
  exact g.chosen_level hU E L hL

/-- Every node of the next relative layer stays inside U. -/
theorem relativeNextLayer_subset
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f) (hroot : level root = f 0)
    (E P : Set CoordNode) (hEU : E ⊆ U)
    (i L : Nat) (hL : i + 1 ≤ L) :
    relativeNextLayer hU E P i L hL ⊆ U := by
  intro z hz
  rcases hz with ⟨g, rfl⟩
  exact g.chosen_mem hU hf hroot E hEU L hL

/-- Spherical finiteness persists for the next relative layer. -/
theorem relativeNextLayer_finite
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (E P : Set CoordNode) (i L : Nat) (hL : i + 1 ≤ L) :
    (relativeNextLayer hU E P i L hL).Finite := by
  apply (level_finite (f L)).subset
  intro z hz
  exact relativeNextLayer_level hU E P i L hL z hz

/-- Every relative child cone has a chosen representative. -/
theorem relativeNextLayer_child_exists
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f)
    (E P : Set CoordNode)
    (i L : Nat) (hL : i + 1 ≤ L)
    (p : CoordNode) (hp : p ∈ P) (hpLevel : level p = f i)
    (t : CoordNode) (ht : t ∈ U)
    (htLevel : level t = f (i + 1)) (hpt : p ≤ t) :
    ∃ z : CoordNode, z ∈ relativeNextLayer hU E P i L hL ∧
      t ≤ z := by
  let g : RelativeGapChild U P f i :=
    ⟨p, hp, hpLevel, t, ht, htLevel, hpt⟩
  exact ⟨g.chosen hU E L hL, ⟨g, rfl⟩,
    g.child_le_chosen hU hf E L hL⟩

/-- Future prescribed nodes remain above selected representatives
in their U-relative cones. -/
theorem relativeNextLayer_protects
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f) (hrootLevel : level root = f 0)
    (E P : Set CoordNode) (hE : MeetClosed E) (hEU : E ⊆ U)
    (i L : Nat) (hL : i + 1 ≤ L)
    (hgap : AvoidsOpenLevelGap E (f i) (f L))
    (p : CoordNode) (hp : p ∈ P) (hpU : p ∈ U)
    (hpLevel : level p = f i)
    (x : CoordNode) (hx : x ∈ E)
    (hpx : p ≤ x) (hxL : f L ≤ level x) :
    ∃ z : CoordNode, z ∈ relativeNextLayer hU E P i L hL ∧
      z ≤ x := by
  have hxU : x ∈ U := hEU hx
  obtain ⟨j, hxLevel⟩ := hU.selected_levels x hxU
  have hLj : L ≤ j := by
    by_contra hnot
    have hjL : j < L := Nat.lt_of_not_ge hnot
    have hstrict := hf hjL
    rw [hxLevel] at hxL
    omega
  have hij : i + 1 ≤ j := hL.trans hLj
  obtain ⟨t, ht, htLevel, htx⟩ :=
    infiniteStrongPicture_next_selected_below hU hf i j hij
      p x hpU hpLevel hxU hxLevel hpx
  have hpt : p ≤ t := by
    rcases lower_linear hpx htx with hpt | htp
    · exact hpt
    · have hlevels := level_le_of_le htp
      rw [hpLevel, htLevel] at hlevels
      have hstrict : f i < f (i + 1) :=
        hf (Nat.lt_succ_self i)
      exact (not_le_of_gt hstrict) hlevels
  let g : RelativeGapChild U P f i :=
    ⟨p, hp, hpLevel, t, ht, htLevel, hpt⟩
  refine ⟨g.chosen hU E L hL, ⟨g, rfl⟩, ?_⟩
  exact relativeProtectedChoice_below_prescribed hU hf E hE
    i L hL hgap t ht htLevel x hx htx hxL

/-- Each retained relative child cone has EXACTLY one representative
on the next selected level. This uses equality of relative-level
children of the same later U-node, independently of the old parent. -/
theorem relativeNextLayer_unique_child
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f)
    (E P : Set CoordNode)
    (i L : Nat) (hL : i + 1 ≤ L)
    (p : CoordNode) (hp : p ∈ P) (hpLevel : level p = f i)
    (t : CoordNode) (ht : t ∈ U)
    (htLevel : level t = f (i + 1)) (hpt : p ≤ t) :
    ∃! z : CoordNode, z ∈ relativeNextLayer hU E P i L hL ∧
      t ≤ z := by
  let g : RelativeGapChild U P f i :=
    ⟨p, hp, hpLevel, t, ht, htLevel, hpt⟩
  refine ⟨g.chosen hU E L hL, ?_, ?_⟩
  · exact ⟨⟨g, rfl⟩, g.child_le_chosen hU hf E L hL⟩
  · intro z hz
    rcases hz with ⟨⟨g', hgz⟩, htz⟩
    subst z
    have hsame : g'.child = t := by
      rcases lower_linear (g'.child_le_chosen hU hf E L hL) htz with h | h
      · exact eq_of_le_of_level_eq h (g'.child_level.trans htLevel.symm)
      · exact (eq_of_le_of_level_eq h (htLevel.trans g'.child_level.symm)).symm
    change relativeProtectedChoice hU E i L hL
      g'.child g'.child_mem g'.child_level =
      relativeProtectedChoice hU E i L hL t ht htLevel
    cases hsame
    rfl

/-- Every chosen representative has a parent at the preceding
selected layer and stays above that parent. -/
theorem relativeNextLayer_has_parent
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f) (E P : Set CoordNode)
    (i L : Nat) (hL : i + 1 ≤ L)
    (z : CoordNode) (hz : z ∈ relativeNextLayer hU E P i L hL) :
    ∃ p : CoordNode, p ∈ P ∧ p ≤ z := by
  rcases hz with ⟨g, rfl⟩
  exact ⟨g.parent, g.parent_mem, g.parent_le_chosen hU hf E L hL⟩

/-- A prescribed E-node on the new selected level remains literally
in the next relative layer once its previous ancestor is retained. -/
theorem relativeNextLayer_contains_prescribed
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f) (hrootLevel : level root = f 0)
    (E P : Set CoordNode) (hE : MeetClosed E) (hEU : E ⊆ U)
    (i L : Nat) (hL : i + 1 ≤ L)
    (hgap : AvoidsOpenLevelGap E (f i) (f L))
    (p : CoordNode) (hp : p ∈ P) (hpU : p ∈ U)
    (hpLevel : level p = f i)
    (x : CoordNode) (hx : x ∈ E)
    (hpx : p ≤ x) (hxLevel : level x = f L) :
    x ∈ relativeNextLayer hU E P i L hL := by
  obtain ⟨z, hz, hzx⟩ :=
    relativeNextLayer_protects hU hf hrootLevel E P hE hEU
      i L hL hgap p hp hpU hpLevel x hx hpx (by omega)
  have hzl := relativeNextLayer_level hU E P i L hL z hz
  have hzxEq : z = x :=
    eq_of_le_of_level_eq hzx (hzl.trans hxLevel.symm)
  rw [← hzxEq]
  exact hz


end CoordNode
end ThreeUniformDiaries
