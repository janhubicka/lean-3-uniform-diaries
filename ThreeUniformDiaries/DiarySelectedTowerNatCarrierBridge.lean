import ThreeUniformDiaries.DiaryFiniteOrderTowerNatCarrierCriterion
import ThreeUniformDiaries.DiaryUniversalTowerAllHorizonPullbacks

/-!
# Track B: specialize the exact finite-order Nat-carrier criterion
# to the ACTUAL selected strong finite absorber tower

No abstract unknown tower is inserted: the finite frames, successor
maps and all-horizon composites are exactly the previously checked
universalStrongAbsorberTower data. We obtain an explicit iff between
a coherent Nat-order realization of the selected target tower and
horizon-uniform numerical rank bounds for every fixed old vertex.

The theorem is purely about the order carrier. It does not prove
those rank bounds, construct the RoleDiary colimit, identify countable
target flips, or establish countable-source flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Actual chosen strong absorber target tower, forgetting the
diary edge/role/meet structure but retaining its exact finite frames
and selected bounded transition maps. -/
noncomputable def selectedAbsorberFiniteOrderTower :
    FiniteOrderTransitionTower where
  size := fun n => (universalStrongAbsorberTower n).bound
  step := universalStrongAbsorberTower_stepMap
  step_strict := by
    intro n u v huv _
    exact (universalStrongAbsorberTower_stepMap_spec n).toMeetEmbedding.strictMono huv
  step_bound := by
    intro n u hu
    exact (universalStrongAbsorberTower_stepMap_spec n).image_bound u hu

/-- The abstract composite is literally the ACTUAL previously verified
selected tower map. There is no change of transition choices. -/
theorem selectedAbsorberFiniteOrderTower_forward_eq
    (n k u : Nat) :
    selectedAbsorberFiniteOrderTower.forward n k u =
      universalStrongAbsorberTower_forwardMap n k u := rfl

/-- Fully explicit numerical carrier criterion for the genuine selected
finite strong absorber target tower. Every quantifier ranges only over
real finite source frames and all later finite horizons. -/
theorem selectedAbsorberTower_natOrder_iff_bounded_ranks :
    selectedAbsorberFiniteOrderTower.NatOrderRealization ↔
      ∀ n u : Nat, u < (universalStrongAbsorberTower n).bound →
        ∃ M : Nat, ∀ k : Nat,
          universalStrongAbsorberTower_forwardMap n k u < M := by
  change selectedAbsorberFiniteOrderTower.NatOrderRealization ↔
    selectedAbsorberFiniteOrderTower.BoundedRanks
  exact selectedAbsorberFiniteOrderTower.natOrderRealization_iff_boundedRanks

end DiaryLeafPriority
end ThreeUniformDiaries
