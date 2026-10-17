import ThreeUniformDiaries.DiaryOnePassStrictIndexedLex
import ThreeUniformDiaries.DiaryOnePassDefaultLexPreservation
import ThreeUniformDiaries.DiaryOnePassSelectedEventRealization

/-!
# Lex order preserved between every pair of distinct realised sibling germs

Fix a source LEAF m, with two actual source leaves u,v at/above m
having the same source singleton type below m but distinct genuine
successor germ codes. Exactly one germ per nonempty parent fibre
is designated as the all-zero default. Every other realised germ
is selected and has a true fresh singleton event before old m.

Three exhaustive cases now establish source-to-target LexEarlier:
  1. both children selected -- the actual indexed/ranked theorem;
  2. first child selected, second default -- the default theorem;
  3. first child default, second selected -- reversed default theorem.

This includes the terminal singleton child u=m and proper normal
successors, without source S1/S2 or a target diary assumption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- Every realised unselected germ is EXACTLY the chosen default
of its source singleton parent. -/
theorem onePass_realOneGerm_not_selected_is_default
    (H : Ordered3Graph Nat) (m : Nat)
    (g : OneGermSpace m)
    (hReal : g ∈ realisedOneGerms H m)
    (hNot : g ∉ selectedOneGerms H m) :
    oneDefaultGerm H m g.1 = some g := by
  classical
  by_contra hBad
  apply hNot
  exact (selectedOneGerm_mem_iff H m g).mpr
    ⟨hReal, fun heq => hBad heq.symm⟩

/-- The true one-pass target preserves source lex ordering for ANY
distinct realised singleton child germs of the same m-parent
when the original vertex m is a leaf. Includes terminal/default
and both-selected cases; no rank premise remains. -/
theorem onePass_leafBlock_siblings_preserve_sourceLex
    (P : RolePrediary H) (m u v : Nat)
    (hm : IsLeaf H m)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m ≤ u) (hmv : m ≤ v)
    (hParent : oneCode H m u = oneCode H m v)
    (hDifferent : oneGermCode H m u ≠
      oneGermCode H m v) :
    LexEarlier (onePassRawTarget H)
      (onePassOldImage H u) (onePassOldImage H v) ↔
        LexEarlier H u v := by
  classical
  let g := oneGermCode H m u
  let h := oneGermCode H m v
  have hParentG : g.1 = h.1 := hParent
  have hNe : g ≠ h := hDifferent
  have hgReal : g ∈ realisedOneGerms H m := by
    simp only [realisedOneGerms, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨u,hu,hmu,rfl⟩
  have hhReal : h ∈ realisedOneGerms H m := by
    simp only [realisedOneGerms, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨v,hv,hmv,rfl⟩
  by_cases hgSelected : g ∈ selectedOneGerms H m
  · obtain ⟨i,hi⟩ :=
      selected_oneGerm_occurs_as_event H m hm g hgSelected
    by_cases hhSelected : h ∈ selectedOneGerms H m
    · obtain ⟨j,hj⟩ :=
        selected_oneGerm_occurs_as_event H m hm h hhSelected
      have hIndexNe : i ≠ j := by
        intro heq
        subst j
        have hEqLabel : BlockEvent.singleton m g =
            BlockEvent.singleton m h := hi.symm.trans hj
        exact hNe (by cases hEqLabel; rfl)
      by_cases hij : i.val < j.val
      · exact (onePass_twoSelected_preserves_sourceLex
          P m i j g h hi hj hij hParentG u v
          hu hv hmu hmv rfl rfl).1
      · have hji : j.val < i.val := by
          have hNeVal : i.val ≠ j.val := by
            intro heq
            exact hIndexNe (Fin.ext heq)
          omega
        exact (onePass_twoSelected_preserves_sourceLex
          P m j i h g hj hi hji hParentG.symm v u
          hv hu hmv hmu rfl rfl).2
    · have hDefault : oneDefaultGerm H m h.1 = some h :=
        onePass_realOneGerm_not_selected_is_default
          H m h hhReal hhSelected
      exact (onePass_fresh_selected_default_preserves_sourceLex
        P m i g h hi hDefault hParentG.symm
        u v hu hv hmu hmv rfl rfl hNe.symm).1
  · have hDefault : oneDefaultGerm H m g.1 = some g :=
      onePass_realOneGerm_not_selected_is_default
        H m g hgReal hgSelected
    have hhSelected : h ∈ selectedOneGerms H m := by
      apply (selectedOneGerm_mem_iff H m h).mpr
      refine ⟨hhReal, ?_⟩
      intro hEqDef
      have hOtherDefault : oneDefaultGerm H m h.1 = some g := by
        rw [← hParentG]
        exact hDefault
      have hEq : some h = some g :=
        hEqDef.trans hOtherDefault
      exact hNe (Option.some.inj hEq).symm
    obtain ⟨j,hj⟩ :=
      selected_oneGerm_occurs_as_event H m hm h hhSelected
    exact (onePass_fresh_selected_default_preserves_sourceLex
      P m j h g hj hDefault hParentG
      v u hv hu hmv hmu rfl rfl hNe).2

end DiaryLeafPriority
end ThreeUniformDiaries
