import ThreeUniformDiaries.DiaryGenericFiniteOldSupportUnboundedNextLeaf
import ThreeUniformDiaries.DiaryReservedOldColourTailDichotomy
import ThreeUniformDiaries.DiaryFullNewGeneratorProfileStabilisation

/-!
# Track D: a saturated cofinal GOOD old-cut mixed colour of genuine successors

The positive finite-old-tuple avoidance / finite-source unavoidability
theorem has shown: for every genuine new source diary leaf with a
nonempty earlier selected leaf prefix, one can CHOOSE a complete old
reserved finite support f having arbitrarily large genuine compatible
reserved immediate next-leaf images in the original unordered generic
target leaf range F.

The existing fully verified tail replacement theorem says that
among true F-range leaves of one COMPLETE mixed singleton colour at
the old-stage-fixed cut B = oldStageTailCut H m f, any sufficiently
numerically late value of a valid immediate successor image is itself
a valid immediate successor, with the SAME literal old support f.

A finite palette / downward recurrence argument now produces ONE
complete mixed colour c for which:
  * actual genuine compatible reserved immediate successors of colour c
    exist at arbitrarily large target numerical positions; and
  * beyond ONE fixed finite threshold T, EVERY genuine leaf in the
    original F-range of colour c is an actual reserved immediate
    successor compatible with the SAME selected old support f.

Thus a cofinal good colour is eventually SATURATED, not just an
arbitrarily late chosen sequence of valid images.

This does NOT imply that its colour class contains an induced generic
3-hypergraph selfcopy, nor that any fixed next image survives later
source horizons. In particular no countable unavoidability or full
big Ramsey theorem is inferred.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Any old fixed support f admitting arbitrarily late genuine reserved
compatible next-leaf images has ONE complete old-cut colour c whose
F-range leaves recur cofinally with genuine reserved successors.
Moreover beyond one finite threshold T, ALL F-range true leaves of
the SAME c have genuine old-compatible reserved next-leaf stages.

No genericity of the original F-range is needed here. The hypothesis
is a genuine cofinal immediate-successor property, not persistence
across longer source horizons. -/
theorem exists_saturated_cofinal_good_old_cut_colour
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (hUnbounded : ∀ M : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
      M < F t ∧
      ReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g ∧
      g m = F t) :
    ∃ c : Fin (oldStageTailCut H m f) →
        Fin (oldStageTailCut H m f) → Bool,
      (∀ M : Nat, ∃ t : Nat,
        M < F t ∧
        DiaryLowerBoundColors.singletonColour K
          (oldStageTailCut H m f) (F t) = c ∧
        HasCompatibleReservedNextLeaf H K F f m (F t)) ∧
      (∃ T : Nat, ∀ t : Nat, T ≤ F t →
        DiaryLowerBoundColors.singletonColour K
          (oldStageTailCut H m f) (F t) = c →
        HasCompatibleReservedNextLeaf H K F f m (F t)) := by
  classical
  let B := oldStageTailCut H m f
  let C := Fin B → Fin B → Bool
  let R : C → Nat → Prop := fun c M =>
    ∃ t : Nat,
      M < F t ∧
      DiaryLowerBoundColors.singletonColour K B (F t) = c ∧
      HasCompatibleReservedNextLeaf H K F f m (F t)
  have hDown : ∀ (c : C) (M N : Nat),
      N ≤ M → R c M → R c N := by
    intro c M N hNM
    rintro ⟨t,hHigh,hColour,hGood⟩
    exact ⟨t,lt_of_le_of_lt hNM hHigh,hColour,hGood⟩
  have hCover : ∀ M : Nat,
      ∃ c : C, c ∈ (Finset.univ : Finset C) ∧ R c M := by
    intro M
    obtain ⟨t,g,hHigh,Q,hOld,hAtM⟩ := hUnbounded M
    refine ⟨DiaryLowerBoundColors.singletonColour K B (F t),
      Finset.mem_univ _,t,hHigh,rfl,?_⟩
    exact ⟨g,Q,hOld,hAtM⟩
  obtain ⟨c,_hc,hRecur⟩ :=
    finite_choice_persistent_of_downward_type
      (Finset.univ : Finset C) R hDown hCover
  obtain ⟨t₀,hHigh₀,hColour₀,hGood₀⟩ := hRecur 0
  refine ⟨c,?_,F t₀,?_⟩
  · intro M
    exact hRecur M
  · intro t hLater hColour
    exact compatible_reserved_nextLeaf_tail_of_oldCut_colour
      hm hGood₀ hLater (hFLeaf t) ⟨t,rfl⟩
      (hColour₀.trans hColour.symm)

/-- Stronger positive consequence under the exact original generic
leaf-range hypotheses: at every NEW source leaf with at least one
selected old leaf, SOME complete literal old support f and ONE
full mixed singleton colour c satisfy BOTH:
  (i) cofinally many genuine F-range leaves of c are valid reserved
      immediate next-leaf images extending f; and
 (ii) EVERY sufficiently late F-range leaf of c is such a valid image.

The chosen f and c may depend on the new source leaf m and cannot be
prescribed in advance. This is not any persistent next-stage map. -/
theorem RoleDiary.exists_chosen_old_support_with_saturated_good_colour
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (hm : IsLeaf H m)
    (hOldNonempty : (countableDiaryLeafPrefix H m).Nonempty) :
    ∃ f : Nat → Nat,
      ReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      ∃ c : Fin (oldStageTailCut H m f) →
          Fin (oldStageTailCut H m f) → Bool,
        (∀ M : Nat, ∃ t : Nat,
          M < F t ∧
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (F t) = c ∧
          HasCompatibleReservedNextLeaf H K
            (fun t : Nat => F t) f m (F t)) ∧
        (∃ T : Nat, ∀ t : Nat, T ≤ F t →
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (F t) = c →
          HasCompatibleReservedNextLeaf H K
            (fun t : Nat => F t) f m (F t)) := by
  obtain ⟨f,Pf,hUnbounded⟩ :=
    DH.exists_some_fixed_old_support_with_unbounded_reserved_next_leaf
      DK G F hFLeaf m hm hOldNonempty
  obtain ⟨c,hRecur,hSat⟩ :=
    exists_saturated_cofinal_good_old_cut_colour
      hm hFLeaf hUnbounded
  exact ⟨f,Pf,c,hRecur,hSat⟩

end DiaryLeafPriority
end ThreeUniformDiaries
