import ThreeUniformDiaries.RelativeFiniteStrongCompletion

/-!
# Infinite protected strong completion INSIDE a chosen strong U

The relative protected layers have ambient meet closure on every
finite prefix. Their union gives the infinite-height counterpart:
a meet-closed strong picture V wholly contained in U, occupying
exactly the selected relative levels sigma(i) and retaining all
prescribed E nodes.

This is the geometric infinite strong-completion existence result,
independent of the subsequent canonical-map composition identity.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The union of all protected U-relative completion layers. -/
noncomputable def relativeCompletedInfinitePicture
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (E : Set CoordNode)
    (sigma : Nat → Nat) (hsigma : StrictMono sigma)
    (r : CoordNode) : Set CoordNode :=
  {x | ∃ i : Nat,
    x ∈ relativeCompletionLayers hU E sigma hsigma r i}

/-- Exact geometric infinite strongness *relative to U*,
including ordinary ambient meet closure. -/
structure RelativeInfiniteStrongPicture
    (V U : Set CoordNode) (f sigma : Nat → Nat)
    (r : CoordNode) : Prop where
  subset_U : V ⊆ U
  meet_closed : MeetClosed V
  root_mem : r ∈ V
  root_le : ∀ x ∈ V, r ≤ x
  selected_levels : ∀ x ∈ V,
    ∃ i : Nat, level x = f (sigma i)
  all_levels : ∀ i : Nat, ∃ x ∈ V,
    level x = f (sigma i)
  next_child : ∀ (i : Nat) (p : CoordNode),
    p ∈ V → level p = f (sigma i) →
    ∀ t : CoordNode, t ∈ U →
      level t = f (sigma i + 1) → p ≤ t →
      ∃! z : CoordNode,
        z ∈ V ∧ level z = f (sigma (i + 1)) ∧ t ≤ z

/-- The union of protected layers gives a literal infinite
strong completion inside U, preserving all prescribed E-nodes. -/
theorem exists_relative_infinite_strong_completion
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f) (hrootLevel : level root = f 0)
    (E : Set CoordNode) (hE : MeetClosed E) (hEU : E ⊆ U)
    (sigma : Nat → Nat) (hsigma : StrictMono sigma)
    (hlevels : ∀ x ∈ E,
      ∃ i : Nat, level x = f (sigma i))
    (r : CoordNode) (hr : r ∈ U)
    (hrLevel : level r = f (sigma 0))
    (hrBelow : ∀ x ∈ E, r ≤ x) :
    ∃ V : Set CoordNode,
      E ⊆ V ∧ RelativeInfiniteStrongPicture V U f sigma r := by
  let V := relativeCompletedInfinitePicture hU E sigma hsigma r
  have hmono : StrictMono (fun i : Nat => f (sigma i)) :=
    fun i j hij => hf (hsigma hij)
  have hgap : ∀ i : Nat,
      AvoidsOpenLevelGap E (f (sigma i)) (f (sigma (i + 1))) :=
    avoids_gaps_of_selected_levels E
      (fun i : Nat => f (sigma i)) hmono hlevels
  have hEV : E ⊆ V := by
    intro x hx
    obtain ⟨i, hxLevel⟩ := hlevels x hx
    refine ⟨i, ?_⟩
    exact relativeCompletionLayers_contains_prescribed
      hU hf hrootLevel E hE hEU sigma hsigma hgap
      r hr hrLevel hrBelow i x hx hxLevel
  refine ⟨V, hEV, ?_⟩
  constructor
  · -- V stays inside U.
    intro x hx
    rcases hx with ⟨i, hi⟩
    exact (relativeCompletionLayers_subset hU hf hrootLevel
      E hEU sigma hsigma r hr i) hi
  · -- A common finite prefix contains every pair of V-nodes.
    intro x y hx hy
    obtain ⟨i, hxi⟩ := hx
    obtain ⟨j, hyj⟩ := hy
    have hxP : x ∈ relativeCompletionPrefix hU E sigma hsigma
        r (max i j) := ⟨i, Nat.le_max_left i j, hxi⟩
    have hyP : y ∈ relativeCompletionPrefix hU E sigma hsigma
        r (max i j) := ⟨j, Nat.le_max_right i j, hyj⟩
    obtain ⟨k, _, hk⟩ :=
      relativeCompletionPrefix_meetClosed hU hf hrootLevel
        E hEU sigma hsigma r hr hrLevel (max i j) hxP hyP
    exact ⟨k, hk⟩
  · -- The chosen root is in layer zero.
    exact ⟨0, by simp [relativeCompletionLayers]⟩
  · -- Every V-node extends the chosen root.
    intro x hx
    obtain ⟨i, hxi⟩ := hx
    exact relativeCompletionLayers_root_le hU hf E
      sigma hsigma r i x hxi
  · -- Every V-node occupies a selected level.
    intro x hx
    obtain ⟨i, hxi⟩ := hx
    exact ⟨i, relativeCompletionLayers_level
      hU E sigma hsigma r hrLevel i x hxi⟩
  · -- Every selected level is nonempty.
    intro i
    obtain ⟨x, hxi⟩ :=
      relativeCompletionLayers_nonempty hU hf hrootLevel E hEU
        sigma hsigma r hr hrLevel i
    exact ⟨x, ⟨i, hxi⟩,
      relativeCompletionLayers_level hU E sigma hsigma
        r hrLevel i x hxi⟩
  · -- One retained representative per U-relative child cone.
    intro i p hp hpLevel t ht htLevel hpt
    obtain ⟨j, hpj⟩ := hp
    have hjLevel :=
      relativeCompletionLayers_level hU E sigma hsigma
        r hrLevel j p hpj
    have hji : j = i :=
      hsigma.injective (hf.injective (hjLevel.symm.trans hpLevel))
    subst j
    obtain ⟨z, ⟨hzLayer, htz⟩, hunique⟩ :=
      relativeCompletionLayers_unique_child hU hf E sigma hsigma
        r hrLevel i p hpj t ht htLevel hpt
    refine ⟨z, ⟨⟨i + 1, hzLayer⟩, ?_, htz⟩, ?_⟩
    · exact relativeCompletionLayers_level hU E sigma hsigma
        r hrLevel (i + 1) z hzLayer
    · intro y ⟨hy, hyLevel, hty⟩
      obtain ⟨j, hyj⟩ := hy
      have hjLevel :=
        relativeCompletionLayers_level hU E sigma hsigma
          r hrLevel j y hyj
      have hji : j = i + 1 :=
        hsigma.injective (hf.injective (hjLevel.symm.trans hyLevel))
      subst j
      exact hunique y ⟨hyj, hty⟩

end CoordNode
end ThreeUniformDiaries
