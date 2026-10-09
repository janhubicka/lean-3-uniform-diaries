import ThreeUniformDiaries.FiniteCompletionMeetClosure
import ThreeUniformDiaries.PrunedTypeTrees

/-!
# Finite strong-subtree completion preserving a meet-closed picture

This is the abstract finite form of manuscript Observation
obs-subtree in the levelled type-tree forest.

Fix a strictly increasing ambient level map lambda and a meet-closed
prescribed picture E whose nodes lie on finitely many of those levels.
Assume its first selected level contains a common root r. The
protected layer construction gives a FINITE set S such that:
* E ⊆ S literally;
* S is rooted at r and ambient-meet-closed;
* S occupies exactly the prescribed levels;
* every immediate ambient successor cone of each nonlast S-node
  has a UNIQUE node on the next selected level.

In particular S is a finite strong subtree in the manuscript's
set-theoretic sense. The separate canonical-map and Milliken
interfaces still have to consume this concrete construction.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- A prescribed picture confined to selected levels never occupies
any open interval between two consecutive selected levels. -/
theorem avoids_gaps_of_selected_levels
    (E : Set CoordNode)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (hlevels : ∀ x ∈ E, ∃ j : Nat, level x = lambda j)
    (i : Nat) :
    AvoidsOpenLevelGap E (lambda i) (lambda (i + 1)) := by
  intro x hx
  obtain ⟨j, hj⟩ := hlevels x hx
  by_cases hji : j ≤ i
  · left
    rw [hj]
    exact hmono.monotone hji
  · right
    have hij : i + 1 ≤ j := by omega
    rw [hj]
    exact hmono.monotone hij

/-- If a node of the completed finite prefix lies at selected
level lambda i, it must be a member of the i-th layer. -/
theorem completionPrefix_on_layer
    (E : Set CoordNode)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (root : CoordNode) (hroot : level root = lambda 0)
    (i k : Nat) (hi : i ≤ k)
    (z : CoordNode)
    (hz : z ∈ completionPrefix E lambda hmono root k)
    (hlev : level z = lambda i) :
    z ∈ completionLayers E lambda hmono root i := by
  rcases hz with ⟨j, hjk, hzj⟩
  have hjlev :=
    completionLayers_level E lambda hmono root hroot j z hzj
  have hji : j = i := hmono.injective (hjlev.symm.trans hlev)
  subst j
  exact hzj

/-- Every selected layer is nonempty, since the three-coordinate
type tree is pruned and the completion fills every child direction. -/
theorem completionLayers_nonempty
    (E : Set CoordNode)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (root : CoordNode) (hroot : level root = lambda 0)
    (k : Nat) :
    (completionLayers E lambda hmono root k).Nonempty := by
  induction k with
  | zero =>
      exact ⟨root, by simp [completionLayers]⟩
  | succ k ih =>
      obtain ⟨p, hp⟩ := ih
      have hpChild : p ⋖ zeroChild p := by
        apply SuccessorTree.LevelTree.covBy_of_le_level_succ
          (le_zeroChild p)
        exact level_zeroChild p
      obtain ⟨z, ⟨hz, _⟩, _⟩ :=
        completionLayers_unique_child E lambda hmono root hroot
          k p (zeroChild p) hp hpChild
      exact ⟨z, hz⟩

/-- A finite strong picture, expressed directly with the notion of
strong subtree from the manuscript. -/
def FiniteStrongPicture
    (S : Set CoordNode)
    (lambda : Nat → Nat) (k : Nat)
    (root : CoordNode) : Prop :=
  S.Finite ∧ MeetClosed S ∧
    root ∈ S ∧
    (∀ x ∈ S, root ≤ x) ∧
    (∀ x ∈ S, ∃ i : Nat, i ≤ k ∧ level x = lambda i) ∧
    (∀ i : Nat, i ≤ k →
      ∃ x ∈ S, level x = lambda i) ∧
    (∀ i : Nat, i < k →
      ∀ p ∈ S, level p = lambda i →
      ∀ t : CoordNode, p ⋖ t →
      ∃! z : CoordNode,
        z ∈ S ∧ level z = lambda (i + 1) ∧ t ≤ z)

/-- Complete a meet-closed finite picture to a finite strong subtree
on the SAME prescribed level set, keeping all original nodes. -/
theorem exists_finite_strong_completion
    (E : Set CoordNode) (hE : MeetClosed E)
    (lambda : Nat → Nat) (hmono : StrictMono lambda)
    (k : Nat)
    (hlevels : ∀ x ∈ E, ∃ i : Nat,
      i ≤ k ∧ level x = lambda i)
    (root : CoordNode)
    (hrootLevel : level root = lambda 0)
    (hroot : ∀ x ∈ E, root ≤ x) :
    ∃ S : Set CoordNode,
      E ⊆ S ∧ FiniteStrongPicture S lambda k root := by
  let S := completionPrefix E lambda hmono root k
  have hgap : ∀ i : Nat,
      AvoidsOpenLevelGap E (lambda i) (lambda (i + 1)) :=
    avoids_gaps_of_selected_levels E lambda hmono
      (fun x hx => by
        rcases hlevels x hx with ⟨i, _, hi⟩
        exact ⟨i, hi⟩)
  have hES : E ⊆ S := by
    intro x hx
    obtain ⟨i, hik, hxlev⟩ := hlevels x hx
    have hxi :=
      completionLayers_contains_prescribed E hE lambda hmono
        hgap root hrootLevel hroot i x hx hxlev
    exact ⟨i, hik, hxi⟩
  refine ⟨S, hES, ?_⟩
  unfold FiniteStrongPicture
  refine ⟨completionPrefix_finite E lambda hmono root k,
    completionPrefix_meetClosed E lambda hmono root hrootLevel k,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨0, Nat.zero_le k, by simp [completionLayers]⟩
  · intro x hx
    exact completionPrefix_root_le E lambda hmono root k x hx
  · intro x hx
    rcases hx with ⟨i, hik, hxi⟩
    exact ⟨i, hik,
      completionLayers_level E lambda hmono root hrootLevel i x hxi⟩
  · intro i hik
    obtain ⟨x, hx⟩ :=
      completionLayers_nonempty E lambda hmono root hrootLevel i
    exact ⟨x, ⟨i, hik, hx⟩,
      completionLayers_level E lambda hmono root hrootLevel i x hx⟩
  · intro i hik p hp hpLevel t hpt
    have hik1 : i + 1 ≤ k := by omega
    have hpLayer : p ∈ completionLayers E lambda hmono root i :=
      completionPrefix_on_layer E lambda hmono root
        hrootLevel i k (Nat.le_of_lt hik) p hp hpLevel
    obtain ⟨z, ⟨hzLayer, htz⟩, hunique⟩ :=
      completionLayers_unique_child E lambda hmono root
        hrootLevel i p t hpLayer hpt
    have hzS : z ∈ S := ⟨i + 1, hik1, hzLayer⟩
    have hzLevel :=
      completionLayers_level E lambda hmono root
        hrootLevel (i + 1) z hzLayer
    refine ⟨z, ⟨hzS, hzLevel, htz⟩, ?_⟩
    intro y ⟨hyS, hyLev, hty⟩
    have hyLayer : y ∈ completionLayers E lambda hmono root (i + 1) :=
      completionPrefix_on_layer E lambda hmono root hrootLevel
        (i + 1) k hik1 y hyS hyLev
    exact hunique y ⟨hyLayer, hty⟩

end CoordNode
end ThreeUniformDiaries
