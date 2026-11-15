import ThreeUniformDiaries.DiarySecondLeafArbitrarilyHighFavourableRoot
import ThreeUniformDiaries.DiarySecondLeafDeepReservedCone

/-!
# Track A: arbitrarily HIGH favourable roots with arbitrarily DEEP actual reserved siblings

English-first adversarial proof:
3-uniform-diaries/notes/track_a_high_root_deep_reserved_sibling_cones_20261115.md

At the SECOND genuine selected source leaf m with unique earlier
selected leaf a, the verified high-root theorem selects an ACTUAL
fully future-order-reserved old support f, arbitrarily high at a,
and ONE favourable actual target one-split s. This f,s pair is
selected BEFORE all subsequent numerical cone requirements.

The previously verified deep-cone theorem applied to the SAME
original unordered generic F range gives, for EVERY desired target
height M and pairwise one-meet depth L, an INFINITE target-numerically
strictly increasing sequence of actual reserved immediate successors.
All their exact rooted singleton meets with f(a) are s, while every
pair's target singleton meet is a genuine S1 one-split >= L.
Selected-leaf determinacy upgrades agreement on the first source
leaf to literal agreement with f on the whole old S_m support.

This does NOT yield an induced generic E5 subcopy in the resulting
sequence and does NOT fix any new leaf image through future SOURCE
horizons. No countable diary embedding or sharp BRD is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- In the original unordered induced generic target true-leaf range F,
at the SECOND genuine selected source leaf m, for EVERY old target
cutoff A there is ONE complete reserved old stage f with f(a)>A and
ONE favourable target S1 split s<f(a) satisfying the exact source
E2 polarity and both old reserve gaps.

For every L and M, the SAME f,s support infinitely many strictly
target-numerically increasing images of genuine complete reserved
m+1 successors with exact old-root meet s, each fixing the ENTIRE
old supported stage S_m, and whose pairwise S1 meets are >= L.

The infinite sequence may vary with L,M. Nothing asserts its internal
E5 graph is generic, or persistence of one next-leaf image past m+1. -/
theorem RoleDiary.exists_arbitrarily_high_favourable_second_leaf_root_with_deep_reserved_sibling_cones
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (a m : Nat)
    (ha : IsLeaf H a) (hm : IsLeaf H m) (ham : a < m)
    (hOld : countableDiaryLeafPrefix H m = {a})
    (A : Nat) :
    ∃ f : Nat → Nat,
      ReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      A < f a ∧
      ∃ s : Nat,
        IsOneSplit K s ∧ s < f a ∧
        (H.edge 0 (H.oneMeetLevel a m) m ↔
          ¬ K.edge 0 s (f a)) ∧
        H.oneMeetLevel a m ≤ s ∧
        s + (a - H.oneMeetLevel a m) ≤ f a ∧
        (∀ L M : Nat,
          ∃ values : Nat → Nat,
            StrictMono values ∧
            (∀ k : Nat,
              M < values k ∧
              K.oneMeetLevel (f a) (values k) = s ∧
              ∃ t : Nat, ∃ g : Nat → Nat,
                values k = F t ∧
                ReservedDiaryStage H K (fun t : Nat => F t)
                  (m + 1) g ∧
                CofinalDiaryStageCompatible H m f g ∧
                g m = values k) ∧
            (∀ i j : Nat, i < j →
              IsOneSplit K (K.oneMeetLevel (values i) (values j)) ∧
              L ≤ K.oneMeetLevel (values i) (values j))) := by
  classical
  obtain ⟨f, P, hOldHigh, s, hsRole, hsBelow, hBit, hGap1, hGap2,
    hCofinalReserved⟩ :=
    DH.exists_arbitrarily_high_favourable_second_leaf_root_with_cofinal_reserved_images
      DK G F hFLeaf a m ha hm ham hOld A
  refine ⟨f, P, hOldHigh, s, hsRole, hsBelow,
    hBit, hGap1, hGap2, ?_⟩
  have hCofinal : ∀ M : Nat,
      ∃ t : Nat,
        M < F t ∧ K.oneMeetLevel (f a) (F t) = s := by
    intro M
    obtain ⟨t, _g, hHigh, _Q, _hOld, _hNew, hMeet⟩ :=
      hCofinalReserved M
    exact ⟨t, hHigh, hMeet⟩
  intro L M
  obtain ⟨values, hValuesMono, hGood, hDeep⟩ :=
    DH.second_leaf_favourable_split_has_deep_reserved_cone
      DK (fun t : Nat => F t) f a m s ha hm ham hOld P
      hFLeaf hsRole hsBelow hCofinal hBit hGap1 hGap2 L M
  refine ⟨values, hValuesMono, ?_, hDeep⟩
  intro k
  obtain ⟨hHigh, hMeet, t, g, hImage, Q, hOldLeaves, hNew⟩ :=
    hGood k
  have hKeep : CofinalDiaryStageCompatible H m f g :=
    P.1.successor_compatible_of_selected_leaf_agreement
      Q.1 hOldLeaves
  exact ⟨hHigh, hMeet, t, g, hImage, Q, hKeep, hNew⟩

end DiaryLeafPriority
end ThreeUniformDiaries
