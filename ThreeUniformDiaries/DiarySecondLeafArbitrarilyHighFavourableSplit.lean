import ThreeUniformDiaries.DiarySecondLeafArbitrarilyHighFavourableRoot
import ThreeUniformDiaries.DiaryGenericMixedConeIndivisibility
import ThreeUniformDiaries.DiaryExactSingletonColourSplitCut

/-!
# Track A: arbitrarily high old root AND arbitrarily high favourable target S1 split

English-first adversarial proof:
3-uniform-diaries/notes/track_a_arbitrarily_high_favourable_second_leaf_split_20261115.md

The verified unconditional finite ATR vertex-indivisibility theorem
selects one WHOLE induced generic subcopy J of the ORIGINAL
unordered target generic leaf range F, homogeneous for the actual
complete mixed singleton colour below ANY prescribed target cut S.

For ANY TWO DISTINCT genuine target leaves of J, the separately
CI-checked exact full RoleDiary singleton-colour cutoff theorem
then forces oneMeet_K(x,y) >= S.

Apply the checked high-favourable second-source-leaf root theorem
INSIDE J, with arbitrary old image bound A, obtaining one genuine
fully reserved old f, a favourable rooted one-split s, and actual
cofinally late reserved successors with SAME split s. The old
image f(a) and any chosen new image g(m) both lie in J and are
distinct because s < f(a) = oneMeet_K(f(a),f(a)).
Their exact singleton-colour agreement forces S <= s.

Reinterpret both old and successor stages in ORIGINAL F via the
same checked range-weakening lemma now exported unchanged from
the predecessor module. No assumed F target-order monotonicity,
genericity of the favourable s-fibre, bounded future SOURCE
horizons or countable diary unavoidability is introduced.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Arbitrarily high favourable SECOND source-leaf split theorem:
for EVERY prescribed old target leaf cutoff A and target SPLIT
cutoff S, choose ONE genuinely fully reserved old supported map
f and ONE genuine favourable target one-split s with

  A < f(a),   S <= s < f(a).

The source-required E2 right orientation and BOTH old numerical
reserve gaps hold. In the ORIGINAL arbitrary unordered generic
target F range, for EVERY new numerical height M there is an
ACTUAL complete future-order-reserved m+1 successor g, preserving
the ENTIRE old support S_m, with new image F(t)>M and exact
oneMeet_K(f(a),F(t))=s.

The choices f,s depend on A,S, but precede ALL M. The s-fibre is
COFINAL with valid reserved successors, not proved generic-rich.
No fixed new image survives through later source horizons. -/
theorem RoleDiary.exists_arbitrarily_high_favourable_second_leaf_root_and_split
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (a m : Nat)
    (ha : IsLeaf H a) (hm : IsLeaf H m) (ham : a < m)
    (hOld : countableDiaryLeafPrefix H m = {a})
    (A S : Nat) :
    ∃ f : Nat → Nat,
      ReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      A < f a ∧
      ∃ s : Nat,
        IsOneSplit K s ∧ S ≤ s ∧ s < f a ∧
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
  obtain ⟨u, _hu, p, hMono⟩ :=
    exists_generic_selfcopy_in_one_mixed_singleton_cone
      G K S (fun t : Nat => F t)
  let J : Ordered3Graph.UnorderedEmbedding G.graph K :=
    F.comp u.asUnordered
  have hJLeaf (t : Nat) : IsLeaf K (J t) :=
    hFLeaf (u t)
  have hJInF (t : Nat) : ∃ i : Nat, J t = F i :=
    ⟨u t, rfl⟩
  obtain ⟨f, PJ, hOldHigh, s, hsRole, hsBelow,
      hBit, hGap1, hGap2, hCofinalJ⟩ :=
    DH.exists_arbitrarily_high_favourable_second_leaf_root_with_cofinal_reserved_images
      DK G J hJLeaf a m ha hm ham hOld A
  have haSelected : a ∈ countableDiaryLeafPrefix H m := by
    rw [hOld]
    simp
  have haSupported : a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) a haSelected
  obtain ⟨i, hi⟩ := PJ.1.leaf_range a haSupported ha
  have hwLeaf : IsLeaf K (f a) :=
    PJ.1.leaf_role a haSupported ha
  obtain ⟨t₀, _g₀, _hHigh₀, _Q₀, _hKeep₀, _hNew₀, hMeet₀⟩ :=
    hCofinalJ 0
  have hDistinct : f a ≠ J t₀ := by
    intro hSame
    have hMeetSelf := hMeet₀
    rw [← hSame, Ordered3Graph.oneMeetLevel_self] at hMeetSelf
    omega
  have hRootColour :
      DiaryLowerBoundColors.singletonColour K S (f a) = p := by
    rw [hi]
    exact hMono i
  have hColourEq :
      DiaryLowerBoundColors.singletonColour K S (f a) =
        DiaryLowerBoundColors.singletonColour K S (J t₀) :=
    hRootColour.trans (hMono t₀).symm
  have hSplitBound : S ≤ s := by
    have hBound :=
      (DK.singletonColour_eq_iff_cut_le_oneMeet
        hwLeaf (hJLeaf t₀) hDistinct S).mp hColourEq
    rw [hMeet₀] at hBound
    exact hBound
  have PF : ReservedDiaryStage H K
      (fun t : Nat => F t) m f :=
    weaken_reserved_stage_leaf_range PJ hJInF
  refine ⟨f, PF, hOldHigh, s, hsRole, hSplitBound,
    hsBelow, hBit, hGap1, hGap2, ?_⟩
  intro M
  obtain ⟨t, g, hHigh, QJ, hKeep, hNew, hMeet⟩ :=
    hCofinalJ M
  obtain ⟨j, hAtF⟩ := hJInF t
  have QF : ReservedDiaryStage H K
      (fun t : Nat => F t) (m + 1) g :=
    weaken_reserved_stage_leaf_range QJ hJInF
  have hHighF : M < F j := by
    rw [← hAtF]
    exact hHigh
  have hNewF : g m = F j :=
    hNew.trans hAtF
  have hMeetF : K.oneMeetLevel (f a) (F j) = s := by
    rw [← hAtF]
    exact hMeet
  exact ⟨j, g, hHighF, QF, hKeep, hNewF, hMeetF⟩

end DiaryLeafPriority
end ThreeUniformDiaries
