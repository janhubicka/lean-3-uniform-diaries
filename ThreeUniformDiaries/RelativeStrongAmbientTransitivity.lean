import ThreeUniformDiaries.RelativeInfiniteStrongCompletion
import ThreeUniformDiaries.MeetClosedGapRigidity

/-!
# Transitivity: relative infinite strong picture is ambient strong

The geometric completion V⊆U is built using U's immediate relative
successor cones, which may skip many immediate ambient levels.
For the manuscript's canonical maps it must also be strong in the
full ambient type tree.

This is a direct argument. An ambient child cone of a selected V-node
has a unique U-selected child representative by U-strongness, and that
relative U-cone has a retained V representative by V-relative
strongness. Its uniqueness among V-nodes follows from ambient meet
closure of V and the absence of intervening selected V-levels.

Thus the relative strong completion represents precisely the usual
ambient strong subtree needed by the canonical-map recursion.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- A genuinely U-relative infinite strong picture is also a strong
picture in the full ambient type tree, at the composed selected levels. -/
theorem relativeInfiniteStrongPicture_to_ambient
    {U V : Set CoordNode} {f sigma : Nat → Nat}
    {root r : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f) (hsigma : StrictMono sigma)
    (hV : RelativeInfiniteStrongPicture V U f sigma r) :
    InfiniteStrongPicture V (fun i => f (sigma i)) r := by
  have hmono : StrictMono (fun i : Nat => f (sigma i)) :=
    fun i j hij => hf (hsigma hij)
  refine ⟨hV.root_mem, hV.root_le, hV.meet_closed,
    hV.selected_levels, hV.all_levels, ?_⟩
  intro i p hp hpLevel t hcover
  have hpU : p ∈ U := hV.subset_U hp
  obtain ⟨q, ⟨hq, hqLevel, htq⟩, _⟩ :=
    hU.next_child (sigma i) p hpU hpLevel t hcover
  have hpq : p ≤ q := le_trans hcover.le htq
  obtain ⟨z, ⟨hz, hzLevel, hqz⟩, _⟩ :=
    hV.next_child i p hp hpLevel q hq hqLevel hpq
  have htz : t ≤ z := le_trans htq hqz
  refine ⟨z, ⟨hz, hzLevel, htz⟩, ?_⟩
  intro y ⟨hy, hyLevel, hty⟩
  have hlt : f (sigma i) < f (sigma (i + 1)) :=
    hmono (Nat.lt_succ_self i)
  have hgap : AvoidsOpenLevelGap V
      (f (sigma i)) (f (sigma (i + 1))) :=
    avoids_gaps_of_selected_levels V
      (fun j : Nat => f (sigma j)) hmono
      hV.selected_levels i
  have htLevel : f (sigma i) < level t := by
    have hcov := covBy_level hcover
    rw [hpLevel] at hcov
    omega
  exact (unique_above_selected_gap V hV.meet_closed
    (f (sigma i)) (f (sigma (i + 1))) hlt hgap
    z y t hz hy hzLevel hyLevel htz hty htLevel).symm

end CoordNode
end ThreeUniformDiaries
