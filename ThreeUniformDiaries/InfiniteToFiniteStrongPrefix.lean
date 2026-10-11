import ThreeUniformDiaries.InfiniteStrongCompletion
import ThreeUniformDiaries.FiniteStrongCompletion

/-!
# A genuine finite strong picture from the initial layers of an infinite one

Given an infinite strong coordinate picture S with selected levels f,
its intersection with the first k+1 selected levels is a *finite*
strong picture with precisely the same root and selected level map.
Unlike arbitrary truncation of E, this retains all immediate ambient
successor cones up to the final selected level.

This bridges the independently verified infinite geometric
composition theorem to the manuscript's finite-height lemma.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The initial k+1 selected levels of an infinite strong picture. -/
def infiniteStrongPicture_finitePrefix
    (S : Set CoordNode) (f : Nat → Nat) (k : Nat) : Set CoordNode :=
  {x | x ∈ S ∧ level x ≤ f k}

/-- The set of ambient coordinate nodes of bounded level is finite. -/
theorem finite_nodes_of_bounded_level (m : Nat) :
    Set.Finite {x : CoordNode | level x ≤ m} := by
  induction m with
  | zero =>
      apply (level_finite 0).subset
      intro x hx
      exact Nat.eq_zero_of_le_zero hx
  | succ m ih =>
      apply (ih.union (level_finite (m + 1))).subset
      intro x hx
      by_cases hxm : level x ≤ m
      · exact Or.inl hxm
      · right
        change level x = m + 1
        omega

/-- Every infinite strong coordinate picture has a genuine finite
initial strong subtree of height k+1, with no additional assumptions. -/
theorem infiniteStrongPicture_finitePrefix_strong
    {S : Set CoordNode} {f : Nat → Nat} {r : CoordNode}
    (hS : InfiniteStrongPicture S f r)
    (hf : StrictMono f)
    (hr : level r = f 0)
    (k : Nat) :
    FiniteStrongPicture
      (infiniteStrongPicture_finitePrefix S f k) f k r := by
  have hfin : (infiniteStrongPicture_finitePrefix S f k).Finite := by
    apply (finite_nodes_of_bounded_level (f k)).subset
    intro x hx
    exact hx.2
  have hroot : r ∈ infiniteStrongPicture_finitePrefix S f k := by
    refine ⟨hS.root_mem, ?_⟩
    rw [hr]
    exact hf.monotone (Nat.zero_le k)
  have hchildren :
      ∀ i : Nat, i < k →
        ∀ p ∈ infiniteStrongPicture_finitePrefix S f k,
          level p = f i →
          ∀ t : CoordNode, p ⋖ t →
          ∃! z : CoordNode,
            z ∈ infiniteStrongPicture_finitePrefix S f k ∧
              level z = f (i + 1) ∧ t ≤ z := by
    intro i hik p hp hplevel t hpt
    obtain ⟨z, ⟨hz, hzlevel, htz⟩, hunique⟩ :=
      hS.next_child i p hp.1 hplevel t hpt
    have hiz : i + 1 ≤ k := by omega
    have hzPref :
        z ∈ infiniteStrongPicture_finitePrefix S f k :=
      ⟨hz, by rw [hzlevel]; exact hf.monotone hiz⟩
    refine ⟨z, ⟨hzPref, hzlevel, htz⟩, ?_⟩
    intro y ⟨hy, hyLevel, hty⟩
    exact hunique y ⟨hy.1, hyLevel, hty⟩
  refine ⟨hfin, ?_, hroot, ?_, ?_, ?_, hchildren⟩
  · intro x y hx hy
    have hc : ∃ c : CoordNode, c ≤ x ∧ c ≤ y :=
      ⟨r, hS.root_le x hx.1, hS.root_le y hy.1⟩
    exact ⟨hS.meet_closed hx.1 hy.1,
      (level_le_of_le (meet_le_left hc)).trans hx.2⟩
  · intro x hx
    exact hS.root_le x hx.1
  · intro x hx
    obtain ⟨i, hlevel⟩ := hS.selected_levels x hx.1
    have hik : i ≤ k := by
      by_contra hnot
      have hki : k < i := Nat.lt_of_not_ge hnot
      have hlt : f k < f i := hf hki
      have hxBound : level x ≤ f k := hx.2
      rw [hlevel] at hxBound
      omega
    exact ⟨i, hik, hlevel⟩
  · intro i hik
    obtain ⟨x, hx, hlevel⟩ := hS.all_levels i
    exact ⟨x, ⟨hx, by rw [hlevel]; exact hf.monotone hik⟩,
      hlevel⟩

end CoordNode
end ThreeUniformDiaries
