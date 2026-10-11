import ThreeUniformDiaries.RelativeCompletionMeetClosure
import ThreeUniformDiaries.FiniteStrongCompletion

/-!
# A genuine finite strong completion INSIDE a given strong coordinate U

The relative protected construction is now complete at the geometric
level. For a meet-closed E⊆U on finitely many selected relative
U-levels sigma(0),...,sigma(k), with a common selected root r∈U,
we construct a finite V⊆U containing E literally.

The completed V is finite, rooted, ambient-meet-closed, occupies exactly
the chosen ambient levels f(sigma(i)), and for each non-last selected
parent has exactly one node in every relative immediate child cone
of U. Thus it is a strong subtree *of U*, rather than merely of
the surrounding full type tree.

The composition-coding identity will be checked separately.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- A finite selected-height strong subtree, relative to a given
infinite strong coordinate tree U, with its genuine ambient meets. -/
structure RelativeFiniteStrongPicture
    (V U : Set CoordNode) (f sigma : Nat → Nat)
    (k : Nat) (r : CoordNode) : Prop where
  finite : V.Finite
  subset_U : V ⊆ U
  meet_closed : MeetClosed V
  root_mem : r ∈ V
  root_le : ∀ x ∈ V, r ≤ x
  selected_levels : ∀ x ∈ V,
    ∃ i : Nat, i ≤ k ∧ level x = f (sigma i)
  all_levels : ∀ i : Nat, i ≤ k →
    ∃ x ∈ V, level x = f (sigma i)
  next_child : ∀ i : Nat, i < k →
    ∀ p ∈ V, level p = f (sigma i) →
    ∀ t ∈ U, level t = f (sigma i + 1) → p ≤ t →
    ∃! z : CoordNode,
      z ∈ V ∧ level z = f (sigma (i + 1)) ∧ t ≤ z

/-- Every finite meet-closed picture E inside U has a protected
finite strong completion on exactly the prescribed U-relative
selected levels, literally retaining every E-node. -/
theorem exists_relative_finite_strong_completion
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f) (hrootLevel : level root = f 0)
    (E : Set CoordNode) (hE : MeetClosed E) (hEU : E ⊆ U)
    (sigma : Nat → Nat) (hsigma : StrictMono sigma)
    (k : Nat)
    (hlevels : ∀ x ∈ E,
      ∃ i : Nat, i ≤ k ∧ level x = f (sigma i))
    (r : CoordNode) (hr : r ∈ U)
    (hrLevel : level r = f (sigma 0))
    (hrBelow : ∀ x ∈ E, r ≤ x) :
    ∃ V : Set CoordNode,
      E ⊆ V ∧ RelativeFiniteStrongPicture V U f sigma k r := by
  let V := relativeCompletionPrefix hU E sigma hsigma r k
  have hmono : StrictMono (fun i : Nat => f (sigma i)) :=
    fun i j hij => hf (hsigma hij)
  have hgap : ∀ i : Nat,
      AvoidsOpenLevelGap E (f (sigma i)) (f (sigma (i + 1))) :=
    avoids_gaps_of_selected_levels E
      (fun i : Nat => f (sigma i)) hmono
      (fun x hx => by
        rcases hlevels x hx with ⟨i, _, hi⟩
        exact ⟨i, hi⟩)
  have hEV : E ⊆ V := by
    intro x hx
    obtain ⟨i, hik, hxLevel⟩ := hlevels x hx
    have hxi :=
      relativeCompletionLayers_contains_prescribed
        hU hf hrootLevel E hE hEU sigma hsigma hgap
        r hr hrLevel hrBelow i x hx hxLevel
    exact ⟨i, hik, hxi⟩
  refine ⟨V, hEV, ?_⟩
  refine ⟨relativeCompletionPrefix_finite hU E sigma hsigma r k,
    relativeCompletionPrefix_subset hU hf hrootLevel E hEU
      sigma hsigma r hr k,
    relativeCompletionPrefix_meetClosed hU hf hrootLevel
      E hEU sigma hsigma r hr hrLevel k,
    relativeCompletionPrefix_root_mem hU E sigma hsigma r k,
    ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact relativeCompletionPrefix_root_le hU hf E sigma hsigma
      r k x hx
  · intro x hx
    exact relativeCompletionPrefix_selected_level hU E sigma hsigma
      r hrLevel k x hx
  · intro i hik
    obtain ⟨x, hx⟩ :=
      relativeCompletionLayers_nonempty hU hf hrootLevel E hEU
        sigma hsigma r hr hrLevel i
    exact ⟨x, ⟨i, hik, hx⟩,
      relativeCompletionLayers_level hU E sigma hsigma
        r hrLevel i x hx⟩
  · intro i hik p hp hpLevel t ht htLevel hpt
    have hik1 : i + 1 ≤ k := by omega
    have hpLayer :
        p ∈ relativeCompletionLayers hU E sigma hsigma r i :=
      relativeCompletionPrefix_on_layer hU hf E sigma hsigma
        r hrLevel i k (Nat.le_of_lt hik) p hp hpLevel
    obtain ⟨z, ⟨hzLayer, htz⟩, hunique⟩ :=
      relativeCompletionLayers_unique_child hU hf E sigma hsigma
        r hrLevel i p hpLayer t ht htLevel hpt
    have hzV : z ∈ V := ⟨i + 1, hik1, hzLayer⟩
    have hzLevel :=
      relativeCompletionLayers_level hU E sigma hsigma
        r hrLevel (i + 1) z hzLayer
    refine ⟨z, ⟨hzV, hzLevel, htz⟩, ?_⟩
    intro y ⟨hyV, hyLevel, hty⟩
    have hyLayer :
        y ∈ relativeCompletionLayers hU E sigma hsigma r (i + 1) :=
      relativeCompletionPrefix_on_layer hU hf E sigma hsigma
        r hrLevel (i + 1) k hik1 y hyV hyLevel
    exact hunique y ⟨hyLayer, hty⟩

end CoordNode
end ThreeUniformDiaries
