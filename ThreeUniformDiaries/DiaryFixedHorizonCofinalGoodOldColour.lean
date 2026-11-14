import ThreeUniformDiaries.DiaryFixedOldSupportCofinalFiniteHorizon
import ThreeUniformDiaries.DiaryChosenFiniteGoodColourBridge
import ThreeUniformDiaries.DiaryReservedOldColourTailDichotomy

/-!
# Track C: one complete GOOD old-cut colour for ANY FIXED finite source horizon

English-first proof and adversarial quantifier audit:
  janhubicka/3-uniform-diaries PR #345.

Fix ONE finite future source horizon q >= m+1 BEFORE selecting f.
The checked Track D finite-horizon recurrence theorem provides one
complete genuine old RESERVED stage f:S_m with cofinally many ACTUAL
q-horizon stages g extending f and sending the new leaf m to F(t).

The complete mixed old-cut colour palette is finite. Standard
finite downward recurrence fixes ONE colour c with cofinally
many q-horizon reserved witnesses g, all sharing the SAME literal
old support f and full B=oldStageTailCut H m f colour c.

One high q-horizon witness restricts to an actual immediate
RESERVED successor. It anchors c in the exact finite candidate
good palette. Consequently every true F-range c-leaf above B
is a complete BARE finite candidate, and every sufficiently high
such leaf is a genuine compatible immediate m+1 RESERVED successor.

IMPORTANT: the q-horizon witness image can vary with the target
cutoff; the finite-support f and selected c may depend on q.
The tail replacement certifies only IMMEDIATE m+1 reserved
successors, not q-stage validity for EVERY high c-leaf. No
generic induced selfcopy in c, all-horizon persistent next leaf,
countable diary unavoidability or BRD theorem is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For every fixed finite horizon q>=m+1, choose ONE actual
complete reserved old support f and ONE entire complete old-stage
mixed colour c such that:
* actual q-stage reserved witnesses fixing f and of colour c recur
  arbitrarily high in the ORIGINAL unordered generic F range;
* c is in the exact high finite candidate palette for (m,f);
* every true high F-range c leaf satisfies the full finite candidate;
* every sufficiently late true F-range c leaf is an ACTUAL
  compatible reserved IMMEDIATE m+1 successor.

The selected f,c depend on q. No persistence of a fixed image
through arbitrary later source horizons is asserted. -/
theorem RoleDiary.exists_fixed_horizon_cofinal_good_oldCut_colour
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m q : Nat) (hmq : m + 1 ≤ q)
    (hm : IsLeaf H m)
    (hOldNonempty : (countableDiaryLeafPrefix H m).Nonempty) :
    ∃ f : Nat → Nat,
      ReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      ∃ c : Fin (oldStageTailCut H m f) →
          Fin (oldStageTailCut H m f) → Bool,
        (∀ M : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
          M < F t ∧
          ReservedDiaryStage H K (fun t : Nat => F t) q g ∧
          CofinalDiaryStageCompatible H m f g ∧
          g m = F t ∧
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (F t) = c) ∧
        c ∈ goodOldCutCandidateColours H K
          (fun t : Nat => F t) f m ∧
        (∀ w : Nat,
          oldStageTailCut H m f ≤ w →
          IsLeaf K w →
          (∃ t : Nat, w = F t) →
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) w = c →
          FiniteNewLeafCandidateCondition H K
            (fun t : Nat => F t) m f w) ∧
        (∃ T : Nat, ∀ t : Nat, T ≤ F t →
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (F t) = c →
          HasCompatibleReservedNextLeaf H K
            (fun t : Nat => F t) f m (F t)) := by
  classical
  obtain ⟨f, Pf, hQ⟩ :=
    DH.exists_some_fixed_old_support_with_unbounded_new_leaf_at_horizon
      DK G F hFLeaf m q hmq hm hOldNonempty
  let B : Nat := oldStageTailCut H m f
  let C := Fin B → Fin B → Bool
  let R : C → Nat → Prop := fun c M =>
    ∃ t : Nat, ∃ g : Nat → Nat,
      M < F t ∧
      ReservedDiaryStage H K (fun t : Nat => F t) q g ∧
      CofinalDiaryStageCompatible H m f g ∧
      g m = F t ∧
      DiaryLowerBoundColors.singletonColour K B (F t) = c
  have hDown : ∀ (c : C) (M N : Nat),
      N ≤ M → R c M → R c N := by
    intro c M N hNM
    rintro ⟨t,g,hHigh,Q,hOld,hNew,hColour⟩
    exact ⟨t,g,lt_of_le_of_lt hNM hHigh,Q,hOld,hNew,hColour⟩
  have hCover : ∀ M : Nat,
      ∃ c : C, c ∈ (Finset.univ : Finset C) ∧ R c M := by
    intro M
    obtain ⟨t,g,hHigh,Q,hOld,hNew⟩ := hQ M
    exact ⟨DiaryLowerBoundColors.singletonColour K B (F t),
      Finset.mem_univ _,t,g,hHigh,Q,hOld,hNew,rfl⟩
  obtain ⟨c,_hc,hRec⟩ :=
    finite_choice_persistent_of_downward_type
      (Finset.univ : Finset C) R hDown hCover
  have hHorizon (M : Nat) :
      ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        ReservedDiaryStage H K (fun t : Nat => F t) q g ∧
        CofinalDiaryStageCompatible H m f g ∧
        g m = F t ∧
        DiaryLowerBoundColors.singletonColour K B (F t) = c :=
    hRec M
  obtain ⟨t₀,g₀,hHigh₀,Q₀,hOld₀,hNew₀,hColour₀⟩ := hHorizon B
  have QImmediate :
      ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g₀ :=
    Q₀.restrict hmq
  have hGood₀ :
      HasCompatibleReservedNextLeaf H K
        (fun t : Nat => F t) f m (F t₀) :=
    ⟨g₀,QImmediate,hOld₀,hNew₀⟩
  have hFinite₀ :
      FiniteNewLeafCandidateCondition H K
        (fun t : Nat => F t) m f (F t₀) :=
    ((Pf.finite_candidate_iff_compatible_next_leaf DH hm).mpr
      hGood₀).1
  have hPalette :
      c ∈ goodOldCutCandidateColours H K
        (fun t : Nat => F t) f m := by
    simp only [goodOldCutCandidateColours, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨F t₀, Nat.le_of_lt hHigh₀, hFLeaf t₀,
      ⟨t₀,rfl⟩, hFinite₀, hColour₀⟩
  refine ⟨f,Pf,c,?_,hPalette,?_,F t₀,?_⟩
  · intro M
    exact hHorizon M
  · intro w hw hwLeaf hwRange hwColour
    have hMember :
        DiaryLowerBoundColors.singletonColour K B w ∈
          goodOldCutCandidateColours H K
            (fun t : Nat => F t) f m := by
      change DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) w ∈
          goodOldCutCandidateColours H K (fun t : Nat => F t) f m
      rw [hwColour]
      exact hPalette
    exact (Pf.1.full_candidate_iff_good_oldCut_colour
      hm hw hwLeaf hwRange).mpr hMember
  · intro t hLater hColour
    exact compatible_reserved_nextLeaf_tail_of_oldCut_colour
      hm hGood₀ hLater (hFLeaf t) ⟨t,rfl⟩
      (hColour₀.trans hColour.symm)

end DiaryLeafPriority
end ThreeUniformDiaries
