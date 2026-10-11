import ThreeUniformDiaries.RelativeFiniteStrongCompletion
import ThreeUniformDiaries.MeetClosedGapRigidity

/-!
# Transitivity of strong subtrees: the finite relative case

A finite strong V inside U has one retained representative in every
U-relative successor cone. Since U itself is a strong subtree of the
ambient three-type forest, V also satisfies the ordinary ambient
strong subtree condition, with selected levels f ∘ sigma.

The existence of a node in every ambient child cone follows by
lifting first to the unique U-relative successor, then to the V
representative. Its uniqueness follows directly from meet closure
and the absence of occupied V levels in the intervening gap.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Finite U-relative strong pictures satisfy the exact ambient
FiniteStrongPicture interface used by geometric canonical maps. -/
theorem relativeFiniteStrongPicture_to_ambient
    {U V : Set CoordNode} {f sigma : Nat → Nat}
    {root r : CoordNode} {k : Nat}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f) (hsigma : StrictMono sigma)
    (hV : RelativeFiniteStrongPicture V U f sigma k r) :
    FiniteStrongPicture V (fun i => f (sigma i)) k r := by
  have hmono : StrictMono (fun i : Nat => f (sigma i)) :=
    fun i j hij => hf (hsigma hij)
  refine ⟨hV.finite, hV.meet_closed, hV.root_mem,
    hV.root_le, hV.selected_levels, hV.all_levels, ?_⟩
  intro i hik p hp hpLevel t hcover
  have hpU : p ∈ U := hV.subset_U hp
  obtain ⟨q, ⟨hq, hqLevel, htq⟩, _⟩ :=
    hU.next_child (sigma i) p hpU hpLevel t hcover
  have hpq : p ≤ q := le_trans hcover.le htq
  obtain ⟨z, ⟨hz, hzLevel, hqz⟩, _⟩ :=
    hV.next_child i hik p hp hpLevel q hq hqLevel hpq
  have htz : t ≤ z := le_trans htq hqz
  refine ⟨z, ⟨hz, hzLevel, htz⟩, ?_⟩
  intro y ⟨hy, hyLevel, hty⟩
  have hlt : f (sigma i) < f (sigma (i + 1)) :=
    hmono (Nat.lt_succ_self i)
  have hlevels : ∀ x ∈ V,
      ∃ j : Nat, level x = f (sigma j) := by
    intro x hx
    obtain ⟨j, _, hlevel⟩ := hV.selected_levels x hx
    exact ⟨j, hlevel⟩
  have hgap : AvoidsOpenLevelGap V
      (f (sigma i)) (f (sigma (i + 1))) :=
    avoids_gaps_of_selected_levels V
      (fun j : Nat => f (sigma j)) hmono hlevels i
  have htLevel : f (sigma i) < level t := by
    have hcov := covBy_level hcover
    rw [hpLevel] at hcov
    omega
  exact (unique_above_selected_gap V hV.meet_closed
    (f (sigma i)) (f (sigma (i + 1))) hlt hgap
    z y t hz hy hzLevel hyLevel htz hty htLevel).symm

end CoordNode
end ThreeUniformDiaries
