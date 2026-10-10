import ThreeUniformDiaries.FiniteStrongCompletion
import ThreeUniformDiaries.InfiniteCanonicalAux

/-!
# Infinite protected strong completion at prescribed selected levels

The finite completion builds protected layers from a meet-closed E,
looking ahead to every future E-node rather than making arbitrary
choices at unoccupied intermediate levels. These very same layers
already exist at every natural index, with no global finiteness
assumption on E.

Their union is a genuine infinite strong coordinate picture, contains
every node of E literally, and uses exactly the prescribed level set.

This is the geometric infinite half of the completion step required
in Lemma canonicalcomposition in the 3-uniform manuscript.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The union of the protected finite completion layers. -/
noncomputable def completedInfinitePicture
    (E : Set CoordNode) (lambda : Nat → Nat)
    (hmono : StrictMono lambda) (root : CoordNode) :
    Set CoordNode :=
  {z | ∃ i : Nat, z ∈ completionLayers E lambda hmono root i}

/-- Every meet-closed selected-level picture with a common selected
root admits an infinite strong completion preserving the picture
literally, on precisely the same selected ambient levels. -/
theorem exists_infinite_strong_completion
    (E : Set CoordNode) (hE : MeetClosed E)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (hlevels : ∀ x ∈ E, ∃ i : Nat, level x = lambda i)
    (root : CoordNode) (hrootLevel : level root = lambda 0)
    (hroot : ∀ x ∈ E, root ≤ x) :
    ∃ S : Set CoordNode,
      E ⊆ S ∧ InfiniteStrongPicture S lambda root := by
  let S := completedInfinitePicture E lambda hmono root
  have hgap : ∀ i : Nat,
      AvoidsOpenLevelGap E (lambda i) (lambda (i + 1)) :=
    avoids_gaps_of_selected_levels E lambda hmono hlevels
  have hcontain : E ⊆ S := by
    intro x hx
    obtain ⟨i, hli⟩ := hlevels x hx
    refine ⟨i, ?_⟩
    exact completionLayers_contains_prescribed E hE lambda hmono
      hgap root hrootLevel hroot i x hx hli
  refine ⟨S, hcontain, ?_⟩
  constructor
  · -- Selected root belongs to the zeroth layer.
    change ∃ i : Nat,
      root ∈ completionLayers E lambda hmono root i
    exact ⟨0, by simp [completionLayers]⟩
  · -- All chosen nodes are descendants of the selected root.
    intro x hx
    obtain ⟨i, hxi⟩ := hx
    exact completionLayers_root_le E lambda hmono root i x hxi
  · -- Any two nodes occur together in some finite completed prefix.
    intro x y hx hy
    obtain ⟨i, hxi⟩ := hx
    obtain ⟨j, hyj⟩ := hy
    have hxp : x ∈ completionPrefix E lambda hmono root (max i j) :=
      ⟨i, Nat.le_max_left i j, hxi⟩
    have hyp : y ∈ completionPrefix E lambda hmono root (max i j) :=
      ⟨j, Nat.le_max_right i j, hyj⟩
    obtain ⟨k, _, hk⟩ :=
      completionPrefix_meetClosed E lambda hmono root
        hrootLevel (max i j) hxp hyp
    exact ⟨k, hk⟩
  · -- No new levels appear.
    intro x hx
    obtain ⟨i, hxi⟩ := hx
    exact ⟨i, completionLayers_level E lambda hmono root
      hrootLevel i x hxi⟩
  · -- Every selected level is nonempty.
    intro i
    obtain ⟨x, hxi⟩ :=
      completionLayers_nonempty E lambda hmono root hrootLevel i
    exact ⟨x, ⟨i, hxi⟩,
      completionLayers_level E lambda hmono root hrootLevel i x hxi⟩
  · -- Each ambient immediate successor cone gets exactly one node.
    intro i p hp hplevel t hpt
    obtain ⟨j, hpj⟩ := hp
    have hji : j = i := hmono.injective
      ((completionLayers_level E lambda hmono root
        hrootLevel j p hpj).trans hplevel)
    subst j
    obtain ⟨z, ⟨hzLayer, htz⟩, hunique⟩ :=
      completionLayers_unique_child E lambda hmono root
        hrootLevel i p t hpj hpt
    refine ⟨z, ⟨⟨i + 1, hzLayer⟩, ?_, htz⟩, ?_⟩
    · exact completionLayers_level E lambda hmono root
        hrootLevel (i + 1) z hzLayer
    · intro w ⟨hw, hwlevel, htw⟩
      obtain ⟨j, hwj⟩ := hw
      have hji : j = i + 1 := hmono.injective
        ((completionLayers_level E lambda hmono root
          hrootLevel j w hwj).trans hwlevel)
      subst j
      exact hunique w ⟨hwj, htw⟩

end CoordNode
end ThreeUniformDiaries
