import ThreeUniformDiaries.DiarySelectedStableStageExactMeets

/-!
# Track B: genuine finite V1/V2 split witnesses survive the conditional limit

The preceding verified finite-stage stable-rank transport preserves all
actual marker roles and exact numerical S1/S2 meets along the TRUE
selected strong-absorber tower maps, under the still-open bounded-ranks
premise. The jointly surjective stable-rank cocone ensures that EVERY
limit vertex originates in one true finite stage.

Consequently every actual limit one-split and two-split has ACTUAL
finite-stage witness leaves, which transport to genuine countable
limit leaves with the prescribed exact numerical meet. Unlike
literal-prefix compactness, these proofs do not let witnesses escape
to infinity; the entire finite witness tuple stays in one fixed
source frame and is transported by ONE coherent stabilized embedding.

No countable full RoleDiary proof is claimed here: universal V/E/S
clauses and V3 must be checked separately. Bounded ranks remain OPEN.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A stable-rank preimage of an actual nonmarker vertex of the
countable target must itself be a true nonmarker source vertex.
The first three stable ranks are literally 0,1,2. -/
theorem selectedAbsorberTower_stableRank_nonmarker_preimage
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks)
    (n u : Nat)
    (hu : u < (universalStrongAbsorberTower n).bound)
    (hNonmarker :
      3 ≤ selectedAbsorberFiniteOrderTower.stableRank hb n u) :
    3 ≤ u := by
  by_contra hlow
  have huCases : u = 0 ∨ u = 1 ∨ u = 2 := by omega
  obtain ⟨hZero,hOne,hTwo⟩ :=
    selectedAbsorberTower_stableRank_markers hb n
  rcases huCases with h0 | h1 | h2
  · subst u
    rw [hZero] at hNonmarker
    omega
  · subst u
    rw [hOne] at hNonmarker
    omega
  · subst u
    rw [hTwo] at hNonmarker
    omega

/-- The canonical selected finite absorber edge limit satisfies
the genuine V1 EXISTENTIAL one-split-witness clause, conditionally
on bounded ranks. Every limit split is the exact stable-rank image
of an actual old finite split; its two source witness leaves
remain leaves and keep their EXACT numerical singleton meet. -/
theorem selectedAbsorberLimit_oneSplit_witness
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks) :
    let K := selectedAbsorberFiniteEdgeTower.limitGraph
      (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb)
    ∀ s : Nat, IsOneSplit K s →
      ∃ a b : Nat, IsLeaf K a ∧ IsLeaf K b ∧
        s < a ∧ s < b ∧ K.oneMeetLevel a b = s := by
  dsimp only
  let T := selectedAbsorberFiniteOrderTower
  let K := selectedAbsorberFiniteEdgeTower.limitGraph
    (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb)
  have hUnbounded : ∀ r : Nat, ∃ n : Nat, r < T.size n := by
    intro r
    simpa only [T, selectedAbsorberFiniteOrderTower] using
      universalStrongAbsorberTower_unbounded_frame r
  intro s hs
  obtain ⟨n,u,hu,hValue⟩ :=
    T.stableRank_jointly_surjective hb hUnbounded s
  have hNonmarker : 3 ≤ T.stableRank hb n u := by
    rw [hValue]
    exact hs.1
  have hu3 : 3 ≤ u :=
    selectedAbsorberTower_stableRank_nonmarker_preimage hb n u hu
      hNonmarker
  have hsFinite : IsOneSplit (universalStrongAbsorberTower n).graph u := by
    apply (selectedAbsorberFiniteStage_roles_in_conditionalLimit
      hb n u hu3 hu).2.1.mp
    change IsOneSplit K (T.stableRank hb n u)
    rw [hValue]
    exact hs
  obtain ⟨a,b,han,hbn,ha,hbLeaf,hua,hub,hMeet⟩ :=
    (universalStrongAbsorberTower n).diary.prediary.one_split_witness
      u hsFinite hu
  let F := T.stableRank hb n
  refine ⟨F a,F b,?_,?_,?_,?_,?_⟩
  · exact (selectedAbsorberFiniteStage_roles_in_conditionalLimit
      hb n a ha.1 han).1.mpr ha
  · exact (selectedAbsorberFiniteStage_roles_in_conditionalLimit
      hb n b hbLeaf.1 hbn).1.mpr hbLeaf
  · have ht := T.stableRank_strict hb n u a hua han
    simpa only [F,hValue] using ht
  · have ht := T.stableRank_strict hb n u b hub hbn
    simpa only [F,hValue] using ht
  · have ht := (selectedAbsorberFiniteStage_meets_in_conditionalLimit
      hb n).1 a b ha.1 han hbLeaf.1 hbn
    rw [hMeet,hValue] at ht
    exact ht

/-- The genuine V2 EXISTENTIAL witness clause in the conditional
countable limit. The four source leaves of ONE finite target
two-split witness remain genuine limit leaves, and the full
ordered-pair meet transports EXACTLY to the original split rank. -/
theorem selectedAbsorberLimit_twoSplit_witness
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks) :
    let K := selectedAbsorberFiniteEdgeTower.limitGraph
      (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb)
    ∀ s : Nat, IsTwoSplit K s →
      ∃ a b c d : Nat, a < b ∧ c < d ∧
        IsLeaf K a ∧ IsLeaf K b ∧ IsLeaf K c ∧ IsLeaf K d ∧
        s < a ∧ s < c ∧
        K.twoMeetLevel a b c d = s := by
  dsimp only
  let T := selectedAbsorberFiniteOrderTower
  let K := selectedAbsorberFiniteEdgeTower.limitGraph
    (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb)
  have hUnbounded : ∀ r : Nat, ∃ n : Nat, r < T.size n := by
    intro r
    simpa only [T, selectedAbsorberFiniteOrderTower] using
      universalStrongAbsorberTower_unbounded_frame r
  intro s hs
  obtain ⟨n,u,hu,hValue⟩ :=
    T.stableRank_jointly_surjective hb hUnbounded s
  have hNonmarker : 3 ≤ T.stableRank hb n u := by
    rw [hValue]
    exact hs.1
  have hu3 : 3 ≤ u :=
    selectedAbsorberTower_stableRank_nonmarker_preimage hb n u hu
      hNonmarker
  have hsFinite : IsTwoSplit (universalStrongAbsorberTower n).graph u := by
    apply (selectedAbsorberFiniteStage_roles_in_conditionalLimit
      hb n u hu3 hu).2.2.mp
    change IsTwoSplit K (T.stableRank hb n u)
    rw [hValue]
    exact hs
  obtain ⟨a,b,c,d,hab,hcd,han,hbn,hcn,hdn,ha,hbLeaf,hc,hd,
      hua,huc,hMeet⟩ :=
    (universalStrongAbsorberTower n).diary.prediary.two_split_witness
      u hsFinite hu
  let F := T.stableRank hb n
  refine ⟨F a,F b,F c,F d,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact T.stableRank_strict hb n a b hab hbn
  · exact T.stableRank_strict hb n c d hcd hdn
  · exact (selectedAbsorberFiniteStage_roles_in_conditionalLimit
      hb n a ha.1 han).1.mpr ha
  · exact (selectedAbsorberFiniteStage_roles_in_conditionalLimit
      hb n b hbLeaf.1 hbn).1.mpr hbLeaf
  · exact (selectedAbsorberFiniteStage_roles_in_conditionalLimit
      hb n c hc.1 hcn).1.mpr hc
  · exact (selectedAbsorberFiniteStage_roles_in_conditionalLimit
      hb n d hd.1 hdn).1.mpr hd
  · have ht := T.stableRank_strict hb n u a hua han
    simpa only [F,hValue] using ht
  · have ht := T.stableRank_strict hb n u c huc hcn
    simpa only [F,hValue] using ht
  · have ht := (selectedAbsorberFiniteStage_meets_in_conditionalLimit
      hb n).2 a b c d hab hcd
      ha.1 han hbLeaf.1 hbn hc.1 hcn hd.1 hdn
    rw [hMeet,hValue] at ht
    exact ht

end DiaryLeafPriority
end ThreeUniformDiaries
