import ThreeUniformDiaries.FiniteCompletionAncestors
import ThreeUniformDiaries.DistinctParentDescendantMeets

/-!
# Meet closure of the fully saturated finite strong-tree picture

The protected recursive construction chooses one representative of
every child cone at every selected level. This already forces the
union of the first k+1 layers to be meet-closed, independently of
the input picture E. A new node meets an old one at its old parent
(or an earlier old meet). Two new nodes either coincide, diverge
immediately above one parent, or descend from distinct previous
parents; in each case their meet is in the union.

This discharges the ambient meet-closure part of the finite strong
subtree completion. The final concrete strong-tree structure and
coding identities remain separate.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The prefix of completed layers splits into its previous part
and the last completed level. -/
theorem completionPrefix_succ_iff
    (E : Set CoordNode)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (root : CoordNode) (k : Nat) (z : CoordNode) :
    z ∈ completionPrefix E lambda hmono root (k + 1) ↔
      z ∈ completionPrefix E lambda hmono root k ∨
      z ∈ completionLayers E lambda hmono root (k + 1) := by
  constructor
  · rintro ⟨i, hi, hzi⟩
    by_cases hik : i ≤ k
    · exact Or.inl ⟨i, hik, hzi⟩
    · have hieq : i = k + 1 := by omega
      exact Or.inr (by simpa [hieq] using hzi)
  · intro h
    rcases h with ⟨i, hi, hzi⟩ | hzi
    · exact ⟨i, by omega, hzi⟩
    · exact ⟨k + 1, le_rfl, hzi⟩

/-- The finite prefix is monotone in its selected height. -/
theorem completionPrefix_mono
    (E : Set CoordNode)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (root : CoordNode) (i j : Nat) (hij : i ≤ j) :
    completionPrefix E lambda hmono root i ⊆
      completionPrefix E lambda hmono root j := by
  rintro z ⟨t, hti, hz⟩
  exact ⟨t, hti.trans hij, hz⟩

/-- Every completed prefix is rooted at the same selected root. -/
theorem completionPrefix_root_le
    (E : Set CoordNode)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (root : CoordNode) (k : Nat)
    (z : CoordNode) (hz : z ∈ completionPrefix E lambda hmono root k) :
    root ≤ z := by
  rcases hz with ⟨i, _, hzi⟩
  exact completionLayers_root_le E lambda hmono root i z hzi

/-- All nodes of a finite completion prefix lie at or below
its maximal selected ambient level. -/
theorem completionPrefix_level_le
    (E : Set CoordNode)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (root : CoordNode) (hroot : level root = lambda 0)
    (k : Nat) (z : CoordNode)
    (hz : z ∈ completionPrefix E lambda hmono root k) :
    level z ≤ lambda k := by
  rcases hz with ⟨i, hik, hzi⟩
  rw [completionLayers_level E lambda hmono root hroot i z hzi]
  exact hmono.monotone hik

/-- The completed finite prefix is closed under the actual
ambient coordinate-tree meet. -/
theorem completionPrefix_meetClosed
    (E : Set CoordNode)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (root : CoordNode) (hroot : level root = lambda 0)
    (k : Nat) :
    MeetClosed (completionPrefix E lambda hmono root k) := by
  induction k with
  | zero =>
      intro x y hx hy
      rcases hx with ⟨i, hi, hx⟩
      rcases hy with ⟨j, hj, hy⟩
      have hi0 : i = 0 := by omega
      have hj0 : j = 0 := by omega
      subst i
      subst j
      change x ∈ ({root} : Set CoordNode) at hx
      change y ∈ ({root} : Set CoordNode) at hy
      have hxeq : x = root := by simpa using hx
      have hyeq : y = root := by simpa using hy
      subst x
      subst y
      exact ⟨0, le_rfl, by
        change meet root root ∈ ({root} : Set CoordNode)
        simpa only [meet_self, Set.mem_singleton_iff]⟩
  | succ k ih =>
      let old := completionPrefix E lambda hmono root k
      let P := completionLayers E lambda hmono root k
      let L := lambda (k + 1)
      let hl : lambda k < L := hmono (Nat.lt_succ_self k)
      have hLift : old ⊆ completionPrefix E lambda hmono root (k + 1) :=
        completionPrefix_mono E lambda hmono root k (k + 1) (Nat.le_succ k)
      have hPold : P ⊆ old := by
        intro p hp
        exact ⟨k, le_rfl, hp⟩
      intro x y hx hy
      have hxs := (completionPrefix_succ_iff E lambda hmono
        root k x).mp hx
      have hys := (completionPrefix_succ_iff E lambda hmono
        root k y).mp hy
      rcases hxs with hxOld | hxNew
      · rcases hys with hyOld | hyNew
        · exact hLift (ih hxOld hyOld)
        · obtain ⟨p, hp, hpy⟩ :=
            completionLayers_has_parent E lambda hmono root k y hyNew
          have hxp : level x ≤ level p := by
            calc
              level x ≤ lambda k :=
                completionPrefix_level_le E lambda hmono root
                  hroot k x hxOld
              _ = level p :=
                (completionLayers_level E lambda hmono root
                  hroot k p hp).symm
          have hc : ∃ c : CoordNode, c ≤ p ∧ c ≤ x :=
            ⟨root,
              completionLayers_root_le E lambda hmono root k p hp,
              completionPrefix_root_le E lambda hmono root k x hxOld⟩
          have hmeet :
              meet x y = meet x p :=
            meet_extension_right x p y hpy hxp hc
          rw [hmeet]
          exact hLift (ih hxOld (hPold hp))
      · rcases hys with hyOld | hyNew
        · obtain ⟨p, hp, hpx⟩ :=
            completionLayers_has_parent E lambda hmono root k x hxNew
          have hyp : level y ≤ level p := by
            calc
              level y ≤ lambda k :=
                completionPrefix_level_le E lambda hmono root
                  hroot k y hyOld
              _ = level p :=
                (completionLayers_level E lambda hmono root
                  hroot k p hp).symm
          have hc : ∃ c : CoordNode, c ≤ p ∧ c ≤ y :=
            ⟨root,
              completionLayers_root_le E lambda hmono root k p hp,
              completionPrefix_root_le E lambda hmono root k y hyOld⟩
          have hmeet : meet x y = meet p y :=
            meet_extension_left p x y hpx hyp hc
          rw [hmeet]
          exact hLift (ih (hPold hp) hyOld)
        · change x ∈ nextLayer E P (lambda k) L hl at hxNew
          change y ∈ nextLayer E P (lambda k) L hl at hyNew
          rcases hxNew with ⟨g, rfl⟩
          rcases hyNew with ⟨g', rfl⟩
          change meet (g.chosen E L hl) (g'.chosen E L hl) ∈
            completionPrefix E lambda hmono root (k + 1)
          have hgp : g.parent ≤ g.chosen E L hl :=
            le_trans g.child_cover.le (g.chosen_extends E L hl)
          have hgp' : g'.parent ≤ g'.chosen E L hl :=
            le_trans g'.child_cover.le (g'.chosen_extends E L hl)
          by_cases hpar : g.parent = g'.parent
          · by_cases hchild : g.child = g'.child
            · obtain ⟨z, hz, hunique⟩ :=
                nextLayer_unique_child E P (lambda k) L hl
                  g.parent g.parent_mem g.parent_level
                  g.child g.child_cover
              have hgmem :
                  g.chosen E L hl ∈ nextLayer E P (lambda k) L hl ∧
                    g.child ≤ g.chosen E L hl :=
                ⟨⟨g, rfl⟩, g.chosen_extends E L hl⟩
              have hgmemp :
                  g'.chosen E L hl ∈ nextLayer E P (lambda k) L hl ∧
                    g.child ≤ g'.chosen E L hl := by
                refine ⟨⟨g', rfl⟩, ?_⟩
                rw [hchild]
                exact g'.chosen_extends E L hl
              have hEq : g.chosen E L hl = g'.chosen E L hl :=
                (hunique _ hgmem).trans (hunique _ hgmemp).symm
              rw [hEq, meet_self]
              exact ⟨k + 1, le_rfl, ⟨g', rfl⟩⟩
            · have hg'cover : g.parent ⋖ g'.child := by
                rw [hpar]
                exact g'.child_cover
              have hmeet :
                  meet (g.chosen E L hl) (g'.chosen E L hl) =
                    g.parent :=
                meet_descendants_distinct_children
                  g.parent g.child g'.child
                  (g.chosen E L hl) (g'.chosen E L hl)
                  g.child_cover hg'cover hchild
                  (g.chosen_extends E L hl)
                  (g'.chosen_extends E L hl)
              rw [hmeet]
              exact hLift (hPold g.parent_mem)
          · have hlev : level g.parent = level g'.parent :=
              g.parent_level.trans g'.parent_level.symm
            have hcommon : ∃ r : CoordNode,
                r ≤ g.parent ∧ r ≤ g'.parent :=
              ⟨root,
                completionLayers_root_le E lambda hmono root k
                  g.parent g.parent_mem,
                completionLayers_root_le E lambda hmono root k
                  g'.parent g'.parent_mem⟩
            have hmeet :=
              meet_descendants_distinct_parents
                g.parent g'.parent
                (g.chosen E L hl) (g'.chosen E L hl)
                hlev hpar hgp hgp' hcommon
            rw [hmeet]
            exact hLift (ih (hPold g.parent_mem)
              (hPold g'.parent_mem))

end CoordNode
end ThreeUniformDiaries
