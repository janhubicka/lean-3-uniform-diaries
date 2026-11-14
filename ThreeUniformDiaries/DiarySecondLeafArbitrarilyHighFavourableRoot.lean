import ThreeUniformDiaries.DiarySecondLeafUnboundedRootFromGenericAvoidance
import ThreeUniformDiaries.DiarySecondLeafCofinalRootedSplitCriterion
import ThreeUniformDiaries.DiaryGenericTargetOldE5PatternCopy

/-!
# Track A: a favourable second-source-leaf rooted split can be chosen arbitrarily HIGH

English-first adversarial proof: 3-uniform-diaries PR #369.

With two genuine selected source leaves a<m, and a the ONLY
earlier selected source leaf, the verified UNCONDITIONAL
favourable second-leaf root theorem supplies some genuine
reserved old stage f and target S1 root s with cofinal genuine
reserved immediate successors.

We quantify the old-root position: for ANY prescribed target
cutoff B, first choose an ACTUAL unordered induced generic
subcopy J of ORIGINAL F[G] whose every genuine target leaf
is above B. Apply the checked favourable second-leaf root
theorem INSIDE this chosen J, obtaining an ACTUAL reserved
old f with f(a)=J(i)>B, a genuine one-split s<f(a),
a cofinal rooted J-fibre and the exact source E2 orientation
and old numerical gap tests.

The independently verified rooted-split cofinal successor
theorem gives actual complete reserved m+1 successors g
inside J with arbitrarily late new images and SAME s,
fixing selected a. Weaken both genuine stages from J to
the ORIGINAL F and use old-selected-leaf agreement to
freeze the entire old source S_m support.

The chosen f and s are fixed BEFORE any new image bound M;
they may depend on B. The favourable s-fibre is only
COFINAL, not established to contain an induced generic
subcopy. No same new image persists through future source
horizons, and no full diary unavoidability is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- UNCONDITIONAL high-root selection for the SECOND true source
diary leaf m with exactly one older selected genuine leaf a.

For EVERY numerical target cutoff B choose ONE genuine old
reserved support f with f(a)>B and one genuine target
one-split s<f(a), satisfying the exact source E2 sign and
both old quantitative reserve gaps. For EVERY further new
target cutoff M there are ACTUAL reserved m+1 successor
stages in the ORIGINAL arbitrary unordered generic F range,
fixing all of f's old support and with new leaf image
F(t)>M meeting f(a) at exactly the SAME s.

The choice f,s is made after B, but before ALL M.
No source-target order monotonicity of F is assumed and
the good s-fibre need not itself be generically rich. -/
theorem RoleDiary.exists_arbitrarily_high_favourable_second_leaf_root_with_cofinal_reserved_images
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (a m : Nat)
    (ha : IsLeaf H a) (hm : IsLeaf H m) (ham : a < m)
    (hOld : countableDiaryLeafPrefix H m = {a})
    (B : Nat) :
    ∃ f : Nat → Nat,
      ReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      B < f a ∧
      ∃ s : Nat,
        IsOneSplit K s ∧ s < f a ∧
        (H.edge 0 (H.oneMeetLevel a m) m ↔
          ¬ K.edge 0 s (f a)) ∧
        H.oneMeetLevel a m ≤ s ∧
        s + (a - H.oneMeetLevel a m) ≤ f a ∧
        (∀ M : Nat,
          ∃ t : Nat, ∃ g : Nat → Nat,
            M < F t ∧
            ReservedDiaryStage H K (fun t : Nat => F t)
              (m + 1) g ∧
            CofinalDiaryStageCompatible H m f g ∧
            g m = F t ∧
            K.oneMeetLevel (f a) (F t) = s) := by
  classical
  obtain ⟨J, hRange, _hMask⟩ :=
    exists_generic_leaf_subcopy_in_prescribed_target_bounded_E5_pattern
      G K F hFLeaf 0 B (fun _ _ => false)
  have hJLeaf (t : Nat) : IsLeaf K (J t) :=
    (hRange t).2.2.1
  have hJInsideF (t : Nat) : ∃ i : Nat, J t = F i :=
    (hRange t).2.2.2
  obtain ⟨f, PJ, s, hsRole, hsBelow, hCone, hBit, hGap1, hGap2⟩ :=
    DH.exists_some_favourable_second_leaf_root_in_generic_range
      DK G J hJLeaf a m ha hm ham hOld
  have haOld : a ∈ countableDiaryLeafPrefix H m := by
    rw [hOld]
    simp
  have haSupported : a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) a haOld
  obtain ⟨i, hAtJ⟩ := PJ.1.leaf_range a haSupported ha
  have hB : B < f a := by
    rw [hAtJ]
    exact (hRange i).1
  have PF : ReservedDiaryStage H K
      (fun t : Nat => F t) m f :=
    PJ.weaken_leaf_range hJInsideF
  refine ⟨f, PF, hB, s, hsRole, hsBelow,
    hBit, hGap1, hGap2, ?_⟩
  intro M
  obtain ⟨j, g, hHigh, hMeet, QJ, hKeep, hNew⟩ :=
    DH.second_leaf_cofinal_successors_of_rooted_split_fibre
      DK (fun t : Nat => J t) f a m s ha hm ham hOld PJ
      hJLeaf hsRole hsBelow hCone hBit hGap1 hGap2 M
  obtain ⟨t, hAtF⟩ := hJInsideF j
  have QF : ReservedDiaryStage H K
      (fun t : Nat => F t) (m + 1) g :=
    QJ.weaken_leaf_range hJInsideF
  have hOldKeep : CofinalDiaryStageCompatible H m f g :=
    PF.1.successor_compatible_of_selected_leaf_agreement
      QF.1 hKeep
  have hHighF : M < F t := by
    rw [← hAtF]
    exact hHigh
  have hNewF : g m = F t :=
    hNew.trans hAtF
  have hMeetF : K.oneMeetLevel (f a) (F t) = s := by
    rw [← hAtF]
    exact hMeet
  exact ⟨t, g, hHighF, QF, hOldKeep, hNewF, hMeetF⟩

end DiaryLeafPriority
end ThreeUniformDiaries
