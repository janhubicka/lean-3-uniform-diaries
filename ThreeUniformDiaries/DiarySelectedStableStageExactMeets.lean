import ThreeUniformDiaries.DiaryFiniteStageUniformStableRanks
import ThreeUniformDiaries.DiaryConditionalEdgeColimitExactPrefixTransfer

/-!
# Track B: complete selected finite-stage role/meet transport into edge colimit

We assume only the OPEN bounded-forward-rank property for the actual
selected strong finite-absorber tower. Every finite old frame
stabilizes SIMULTANEOUSLY under the selected forward maps. We choose
one late horizon past that uniform stabilization cutoff and past one
exact literal edge-prefix cutoff covering the whole stabilized image.

The previously VERIFIED bounded ALL-NUMERICAL-MEET finite embeddings
then transfer every old marker role, singleton meet and full pair meet
to the countable edge-table limit. These are actual finite-source
coordinates (no fictitious global RoleDiary on a zero-extended tail).

The result still does not prove bounded ranks, a full countable
RoleDiary, or countable every-target-flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- All vertices of ONE selected finite stage have their stable
numerical ranks within a COMMON fixed finite prefix, simultaneously
at a horizon where the limit and that actual target stage have
exactly the same raw edge and nonedge table on that prefix. -/
theorem selectedAbsorberTower_commonStableRankAndLiteralPrefix
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks)
    (n : Nat) :
    ∃ k q : Nat,
      (∀ u : Nat, u < (universalStrongAbsorberTower n).bound →
        universalStrongAbsorberTower_forwardMap n k u =
          selectedAbsorberFiniteOrderTower.stableRank hb n u ∧
        selectedAbsorberFiniteOrderTower.stableRank hb n u < q) ∧
      LiteralOldPrefixAgreement
        (selectedAbsorberFiniteEdgeTower.limitGraph
          (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb))
        (universalStrongAbsorberTower (n+k)).graph q := by
  classical
  let F : Nat → Nat :=
    selectedAbsorberFiniteOrderTower.stableRank hb n
  let q : Nat :=
    ((Finset.range (universalStrongAbsorberTower n).bound).sup F) + 1
  have hRange (u : Nat)
      (hu : u < (universalStrongAbsorberTower n).bound) :
      F u < q := by
    have hMem : u ∈ Finset.range (universalStrongAbsorberTower n).bound :=
      Finset.mem_range.mpr hu
    have hLe : F u ≤
        (Finset.range (universalStrongAbsorberTower n).bound).sup F :=
      Finset.le_sup hMem
    dsimp [q]
    omega
  obtain ⟨K,hStable⟩ :=
    selectedAbsorberTower_uniformFiniteStageStableRanks hb n
  let hPrefix :=
    selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb
  let k : Nat := max K (edgePrefixCutoff hPrefix q - n)
  have hK : K ≤ k := le_max_left _ _
  have hCut : edgePrefixCutoff hPrefix q ≤ n+k := by
    dsimp [k]
    omega
  refine ⟨k,q,?_,?_⟩
  · intro u hu
    exact ⟨hStable k hK u hu, hRange u hu⟩
  · exact selectedAbsorberLimit_literalOldPrefix hb q (n+k) hCut

/-- Marker ranks 0,1,2 are LITERALLY fixed in the canonical
selected finite-stage embedding to the countable edge limit.
The source/target stage maps are the actual selected all-meet maps. -/
theorem selectedAbsorberTower_stableRank_markers
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks)
    (n : Nat) :
    selectedAbsorberFiniteOrderTower.stableRank hb n 0 = 0 ∧
    selectedAbsorberFiniteOrderTower.stableRank hb n 1 = 1 ∧
    selectedAbsorberFiniteOrderTower.stableRank hb n 2 = 2 := by
  obtain ⟨k,q,hAlign,_⟩ :=
    selectedAbsorberTower_commonStableRankAndLiteralPrefix hb n
  have hFrame : 3 ≤ (universalStrongAbsorberTower n).bound :=
    (universalStrongAbsorberTower n).diary.prediary.frame.length_ge_three
  let E := (universalStrongAbsorberTower_forwardMap_spec n k).toMeetEmbedding
  constructor
  · exact ((hAlign 0 (by omega)).1.symm).trans E.marker_zero
  constructor
  · exact ((hAlign 1 (by omega)).1.symm).trans E.marker_one
  · exact ((hAlign 2 (by omega)).1.symm).trans E.marker_two

/-- FULL reflection of genuine old marker roles in the countable
edge-table limit, for every real old finite-stage vertex. -/
theorem selectedAbsorberFiniteStage_roles_in_conditionalLimit
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks)
    (n u : Nat)
    (hu3 : 3 ≤ u) (hun : u < (universalStrongAbsorberTower n).bound) :
    let K := selectedAbsorberFiniteEdgeTower.limitGraph
      (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb)
    let F := selectedAbsorberFiniteOrderTower.stableRank hb n
    let B := (universalStrongAbsorberTower n).graph
    (IsLeaf K (F u) ↔ IsLeaf B u) ∧
    (IsOneSplit K (F u) ↔ IsOneSplit B u) ∧
    (IsTwoSplit K (F u) ↔ IsTwoSplit B u) := by
  dsimp only
  obtain ⟨k,q,hAlign,hPrefix⟩ :=
    selectedAbsorberTower_commonStableRankAndLiteralPrefix hb n
  have hFwd := (hAlign u hun).1
  have hRange := (hAlign u hun).2
  have hRoles :=
    role_iff_of_literalOldPrefix hPrefix
      (selectedAbsorberFiniteOrderTower.stableRank hb n u) hRange
  let E := (universalStrongAbsorberTower_forwardMap_spec n k).toMeetEmbedding
  have hLeaf := E.leaf_iff u hu3 hun
  have hOne := E.oneSplit_iff u hu3 hun
  have hTwo := E.twoSplit_iff u hu3 hun
  rw [hFwd] at hLeaf hOne hTwo
  exact ⟨hRoles.1.trans hLeaf,
    hRoles.2.1.trans hOne,
    hRoles.2.2.trans hTwo⟩

/-- Exact preservation of ALL capped numerical singleton meets and
FULL ordered-pair meets along the canonical stable-rank embedding of
a real selected finite absorber stage, simultaneously. This
includes split/leaf and split/split comparisons whenever the
original meet-embedding interface covers them. -/
theorem selectedAbsorberFiniteStage_meets_in_conditionalLimit
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks)
    (n : Nat) :
    let K := selectedAbsorberFiniteEdgeTower.limitGraph
      (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb)
    let F := selectedAbsorberFiniteOrderTower.stableRank hb n
    let B := (universalStrongAbsorberTower n).graph
    (∀ u v : Nat,
      3 ≤ u → u < (universalStrongAbsorberTower n).bound →
      3 ≤ v → v < (universalStrongAbsorberTower n).bound →
      K.oneMeetLevel (F u) (F v) = F (B.oneMeetLevel u v)) ∧
    (∀ a b c d : Nat,
      a < b → c < d →
      3 ≤ a → a < (universalStrongAbsorberTower n).bound →
      3 ≤ b → b < (universalStrongAbsorberTower n).bound →
      3 ≤ c → c < (universalStrongAbsorberTower n).bound →
      3 ≤ d → d < (universalStrongAbsorberTower n).bound →
      K.twoMeetLevel (F a) (F b) (F c) (F d) =
        F (B.twoMeetLevel a b c d)) := by
  dsimp only
  obtain ⟨k,q,hAlign,hPrefix⟩ :=
    selectedAbsorberTower_commonStableRankAndLiteralPrefix hb n
  let E := (universalStrongAbsorberTower_forwardMap_spec n k).toMeetEmbedding
  constructor
  · intro u v hu3 hun hv3 hvn
    have hMeetBound :
        (universalStrongAbsorberTower n).graph.oneMeetLevel u v <
          (universalStrongAbsorberTower n).bound := by
      have hLe := (universalStrongAbsorberTower n).graph.oneMeetLevel_le_min u v
      omega
    have hStage := E.oneMeet u v hu3 hun hv3 hvn
    rw [(hAlign u hun).1, (hAlign v hvn).1,
        (hAlign _ hMeetBound).1] at hStage
    have hPrefixMeet :=
      oneMeetLevel_eq_of_literalOldPrefix hPrefix
        (selectedAbsorberFiniteOrderTower.stableRank hb n u)
        (selectedAbsorberFiniteOrderTower.stableRank hb n v)
        (hAlign u hun).2 (hAlign v hvn).2
    exact hPrefixMeet.trans hStage
  · intro a b c d hab hcd ha3 han hb3 hbn hc3 hcn hd3 hdn
    have hMeetBound :
        (universalStrongAbsorberTower n).graph.twoMeetLevel a b c d <
          (universalStrongAbsorberTower n).bound := by
      have hLe := (universalStrongAbsorberTower n).graph.twoMeetLevel_le_min a b c d
      omega
    have hStage := E.twoMeet a b c d hab hcd
      ha3 han hb3 hbn hc3 hcn hd3 hdn
    rw [(hAlign a han).1, (hAlign b hbn).1,
        (hAlign c hcn).1, (hAlign d hdn).1,
        (hAlign _ hMeetBound).1] at hStage
    have hPrefixMeet :=
      twoMeetLevel_eq_of_literalOldPrefix hPrefix
        (selectedAbsorberFiniteOrderTower.stableRank hb n a)
        (selectedAbsorberFiniteOrderTower.stableRank hb n b)
        (selectedAbsorberFiniteOrderTower.stableRank hb n c)
        (selectedAbsorberFiniteOrderTower.stableRank hb n d)
        (hAlign a han).2 (hAlign b hbn).2
        (hAlign c hcn).2 (hAlign d hdn).2
    exact hPrefixMeet.trans hStage

end DiaryLeafPriority
end ThreeUniformDiaries
