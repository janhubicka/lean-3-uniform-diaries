import ThreeUniformDiaries.DiaryOnePassRoleCoverage
import ThreeUniformDiaries.DiaryOnePassEventReflection

/-!
# Exhaustive leaf preimages and exact fresh-event positive cones

The one-pass raw target uses Nat vertices: not merely an external
list of tagged source vertices and inserted splits. For V1/V2,
positive leaf witnesses and all target leaves must therefore be
identified directly in the actual target hypergraph.

We prove every target leaf is EXACTLY the old image of a source
leaf (both directions, no S1/S2 assumptions). Consequently, the
positive leaf cone of any fresh singleton event is precisely the
source leaf germ selected by the event. Likewise a fresh pair event
is positive precisely on images of ordered source leaf pairs
belonging to its selected complete pair-germ class.

These are actual target-edge equivalences, not assumptions
about synthetic event labels. They permit the witness/coherence
V1/V2 proofs to use source global cut transport and class
separation without losing possible non-original target leaves.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- All actual target leaves, and only target leaves, are images
of old source leaves. No inserted event is inadvertently a leaf. -/
theorem onePassRawTarget_leaf_iff_oldLeaf_image
    (H : Ordered3Graph Nat) (v : Nat) :
    IsLeaf (onePassRawTarget H) v ↔
      ∃ u : Nat, IsLeaf H u ∧ onePassOldImage H u = v := by
  constructor
  · intro hleaf
    rcases onePass_target_index_covered H v with
        ⟨u,hu⟩ | ⟨m,i,he⟩
    · subst v
      exact ⟨u,(onePassRawTarget_old_leaf_iff H u).mp hleaf,rfl⟩
    · subst v
      rcases onePass_event_label_at_own_cut H m i with
          ⟨g,hget⟩ | ⟨g,hget⟩
      · have htwo := onePassRawTarget_fresh_twoSplit H m i g hget
        exact False.elim (hleaf.2.2 htwo.2.2)
      · have hone := onePassRawTarget_fresh_oneSplit H m i g hget
        exact False.elim (hleaf.2.1 hone.2.1)
  · rintro ⟨u,hu,rfl⟩
    exact (onePassRawTarget_old_leaf_iff H u).mpr hu

/-- The positive target LEAF cone at one fresh 1-split consists
exactly of images of original source leaves of its selected
normal/terminal singleton germ. -/
theorem onePassRawTarget_freshOne_positive_leaf_iff
    (H : Ordered3Graph Nat) (m v : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : OneGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.singleton m g) :
    (IsLeaf (onePassRawTarget H) v ∧
      (onePassRawTarget H).edge 0
        (onePassEventPosition H m i) v) ↔
      ∃ u : Nat, IsLeaf H u ∧ m ≤ u ∧
        oneGermCode H m u = g ∧ onePassOldImage H u = v := by
  constructor
  · rintro ⟨hleaf,he⟩
    obtain ⟨u,hu,huv⟩ :=
      (onePassRawTarget_leaf_iff_oldLeaf_image H v).mp hleaf
    subst v
    have hinc :=
      (onePassRawTarget_singleton_incidence_iff H m u i g hget).mp he
    exact ⟨u,hinc.1,hinc.2.1,hinc.2.2,rfl⟩
  · rintro ⟨u,hu,hmu,hg,rfl⟩
    exact ⟨(onePassRawTarget_old_leaf_iff H u).mpr hu,
      (onePassRawTarget_singleton_incidence_iff
        H m u i g hget).mpr ⟨hu,hmu,hg⟩⟩

/-- The positive target leaf-PAIR cone at one fresh 2-split is
exactly the image of original ordered leaf pairs with its
complete selected source pair-germ, including capped pairs. -/
theorem onePassRawTarget_freshTwo_positive_leafPair_iff
    (H : Ordered3Graph Nat) (m v w : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : TwoGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.pair m g) :
    (IsLeaf (onePassRawTarget H) v ∧
      IsLeaf (onePassRawTarget H) w ∧ v < w ∧
      (onePassRawTarget H).edge
        (onePassEventPosition H m i) v w) ↔
      ∃ u t : Nat, IsLeaf H u ∧ IsLeaf H t ∧
        m ≤ u ∧ u < t ∧ twoGermCode H m u t = g ∧
        onePassOldImage H u = v ∧ onePassOldImage H t = w := by
  constructor
  · rintro ⟨hv,hw,hvw,he⟩
    obtain ⟨u,hu,huv⟩ :=
      (onePassRawTarget_leaf_iff_oldLeaf_image H v).mp hv
    obtain ⟨t,ht,htw⟩ :=
      (onePassRawTarget_leaf_iff_oldLeaf_image H w).mp hw
    subst v
    subst w
    have hcode :=
      (onePassRawTarget_pair_incidence_iff
        H m u t i g hget).mp he
    exact ⟨u,t,hcode.1,hcode.2.1,hcode.2.2.1,
      hcode.2.2.2.1,hcode.2.2.2.2,rfl,rfl⟩
  · rintro ⟨u,t,hu,ht,hmu,hut,hg,rfl,rfl⟩
    exact ⟨(onePassRawTarget_old_leaf_iff H u).mpr hu,
      (onePassRawTarget_old_leaf_iff H t).mpr ht,
      (onePassOldImage_strictMono H) hut,
      (onePassRawTarget_pair_incidence_iff
        H m u t i g hget).mpr ⟨hu,ht,hmu,hut,hg⟩⟩

end DiaryLeafPriority
end ThreeUniformDiaries
