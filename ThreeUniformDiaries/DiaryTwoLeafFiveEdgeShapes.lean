import ThreeUniformDiaries.DiaryTwoLeafExactSixSupport
import ThreeUniformDiaries.DiaryFullRoleDefinition

/-!
# Only five increasing edge shapes on a two-leaf support

Given genuine selected leaves a<b in a full role diary, their generated
support is exactly {0,1,2,s,a,b}, where s is their singleton meet.
The manuscript's permitted-edge axiom E1--E5 permits only FIVE of
the twenty increasing triples on this support:

  (0,1,s), (0,s,a), (0,s,b), (1,a,b), (2,a,b).

The first is forced true by the actual one-split role. Of the other
four, the verified two-leaf marker-orientation theorem shows that
one right E2 bit determines all incidences.

This lemma establishes precisely the edge-SHAPE classification, not
the full fixed-new-leaf successor or existence of a target leaf.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- On the canonical support of two selected leaves, any actual edge
must be one of the five marker/split/leaf configurations. This also
rules out the other ten would-be edge shapes without treating them
as independent assumptions. -/
theorem RoleDiary.twoLeafSupportedEdge_shapes
    {H : Ordered3Graph Nat}
    (D : RoleDiary H)
    (a b : Nat)
    (ha : IsLeaf H a) (hb : IsLeaf H b) (hab : a < b)
    (x y z : Nat)
    (hx : x ∈ finiteLeafMeetSupport H ({a,b} : Finset Nat))
    (hy : y ∈ finiteLeafMeetSupport H ({a,b} : Finset Nat))
    (hz : z ∈ finiteLeafMeetSupport H ({a,b} : Finset Nat))
    (he : H.edge x y z) :
    let s := H.oneMeetLevel a b
    (x = 0 ∧ y = 1 ∧ z = s) ∨
    (x = 0 ∧ y = s ∧ (z = a ∨ z = b)) ∨
    ((x = 1 ∨ x = 2) ∧ y = a ∧ z = b) := by
  classical
  let s := H.oneMeetLevel a b
  have hs : IsOneSplit H s :=
    D.singleton_meets a b ha hb (ne_of_lt hab)
  have hCases : ∀ u : Nat,
      u ∈ finiteLeafMeetSupport H ({a,b} : Finset Nat) →
      u < 3 ∨ u = a ∨ u = b ∨ u = s := by
    intro u hu
    rw [D.twoLeafSupport_eq a b ha hb hab] at hu
    simpa only [Finset.mem_union, Finset.mem_range,
      Finset.mem_insert, Finset.mem_singleton] using hu
  have hSupportedLeaf : ∀ u : Nat,
      u ∈ finiteLeafMeetSupport H ({a,b} : Finset Nat) →
      IsLeaf H u → u = a ∨ u = b := by
    intro u hu hLeaf
    rcases hCases u hu with hSmall | hA | hB | hS
    · have h3 := hLeaf.1
      omega
    · exact Or.inl hA
    · exact Or.inr hB
    · have hOne : IsOneSplit H u := by
        rw [hS]
        exact hs
      exact False.elim (hLeaf.2.1 hOne.2.1)
  have hSupportedOne : ∀ u : Nat,
      u ∈ finiteLeafMeetSupport H ({a,b} : Finset Nat) →
      IsOneSplit H u → u = s := by
    intro u hu hOne
    rcases hCases u hu with hSmall | hA | hB | hS
    · have h3 := hOne.1
      omega
    · subst u
      exact False.elim (ha.2.1 hOne.2.1)
    · subst u
      exact False.elim (hb.2.1 hOne.2.1)
    · exact hS
  have hOrd : x < y ∧ y < z := D.edge_ordered x y z he
  rcases D.permitted_edge x y z he with hE1 | hE2 | hE3 | hE4 | hE5
  · rcases hE1 with ⟨rfl, hMark, hz3⟩
    have hzS : z = s := by
      rcases hCases z hz with hSmall | hA | hB | hS
      · omega
      · subst z
        rcases hMark with hY | hY
        · subst y
          exact False.elim (ha.2.1 he)
        · subst y
          exact False.elim (ha.2.2 he)
      · subst z
        rcases hMark with hY | hY
        · subst y
          exact False.elim (hb.2.1 he)
        · subst y
          exact False.elim (hb.2.2 he)
      · exact hS
    have hy1 : y = 1 := by
      rcases hMark with hY | hY
      · exact hY
      · subst y
        rw [hzS] at he
        exact False.elim (hs.2.2 he)
    exact Or.inl ⟨rfl,hy1,hzS⟩
  · rcases hE2 with ⟨rfl, hOne, hLeaf⟩
    have hyS : y = s := hSupportedOne y hy hOne
    have hzAB : z = a ∨ z = b := hSupportedLeaf z hz hLeaf
    exact Or.inr (Or.inl ⟨rfl,hyS,hzAB⟩)
  · have hTwo : IsTwoSplit H x := hE3.1
    exact False.elim
      ((D.no_twoSplit_in_twoLeafMeetSupport a b ha hb hab x hx) hTwo)
  · rcases hE4 with ⟨hX,hY,hZ⟩
    have hyAB : y = a ∨ y = b := hSupportedLeaf y hy hY
    have hzAB : z = a ∨ z = b := hSupportedLeaf z hz hZ
    have hyz : y = a ∧ z = b := by
      rcases hyAB with hYA | hYB <;>
      rcases hzAB with hZA | hZB <;> omega
    exact Or.inr (Or.inr ⟨hX,hyz.1,hyz.2⟩)
  · rcases hE5 with ⟨hX,hY,hZ⟩
    have hxAB : x = a ∨ x = b := hSupportedLeaf x hx hX
    have hyAB : y = a ∨ y = b := hSupportedLeaf y hy hY
    have hzAB : z = a ∨ z = b := hSupportedLeaf z hz hZ
    rcases hxAB with hXA | hXB <;>
    rcases hyAB with hYA | hYB <;>
    rcases hzAB with hZA | hZB <;> omega

end DiaryLeafPriority
end ThreeUniformDiaries
