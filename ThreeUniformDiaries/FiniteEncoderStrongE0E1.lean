import ThreeUniformDiaries.FiniteEncoderRootLevels
import ThreeUniformDiaries.FiniteStrongCompletion

/-!
# Complete the enumeration and singleton-type finite pictures

This is the concrete application of the abstract finite strong-subtree
completion theorem to the first two coordinates of Lemma Aemb.

Both original candidate sets contain every node below the prescribed
fixed prefix, are meet-closed, have a root at the first selected level,
and occupy only selected image levels. Hence each admits a finite
strong-tree picture on precisely the common level map e.

The third (auxiliary-pair) coordinate needs a terminal-node case split
and is handled in a separate module.
-/

namespace ThreeUniformDiaries
namespace EnumNode

/-- The completed E0 picture, stated without a dependent-pair
abbreviation so it can be used directly in finite Aemb coding. -/
theorem exists_finiteEnum_strong_picture
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (e : Ordered3Graph.Embedding A.toOrdered3Graph H.toOrdered3Graph)
    (n : Nat) (hnm : n ≤ m) (hm : 0 < m)
    (hfix : ∀ k < n, e k = k) :
    ∃ r : CoordNode, ∃ S : Set CoordNode,
      (∀ x, finiteEnumCandidate H e n m x → x ∈ S) ∧
      CoordNode.FiniteStrongPicture S e (m - 1) r := by
  let E : Set CoordNode := {x | finiteEnumCandidate H e n m x}
  have hE : CoordNode.MeetClosed E := by
    intro x y hx hy
    exact H.finiteEnumCandidate_meet e e.strictMono n m x y hx hy
  obtain ⟨r, hrootLevel, hroot⟩ :
      ∃ r : CoordNode, CoordNode.level r = e 0 ∧
        ∀ x ∈ E, r ≤ x := by
    by_cases hz : n = 0
    · subst n
      obtain ⟨r, _, hlev, hbelow⟩ :=
        H.finiteEnumCandidate_root_zero e e.strictMono m hm
      exact ⟨r, hlev, fun x hx => hbelow x hx⟩
    · have hn : 0 < n := by omega
      obtain ⟨r, _, hlev, hbelow⟩ :=
        A.finiteEnumCandidate_root_positive H e n hn
      have h0 : e 0 = 0 := hfix 0 hn
      exact ⟨r, by rw [h0]; exact hlev, fun x hx => hbelow x hx⟩
  have hlevels :
      ∀ x ∈ E, ∃ i : Nat, i ≤ m - 1 ∧ CoordNode.level x = e i := by
    intro x hx
    obtain ⟨i, him, hi⟩ :=
      A.finiteEnumCandidate_levels H e n hnm hfix x hx
    exact ⟨i, by omega, hi⟩
  obtain ⟨S, hES, hstrong⟩ :=
    CoordNode.exists_finite_strong_completion E hE
      e e.strictMono (m - 1) hlevels r hrootLevel hroot
  exact ⟨r, S, fun x hx => hES hx, hstrong⟩

/-- The completed E1 picture preserves all selected singleton types,
including the full prescribed initial segment, at their actual target
levels. -/
theorem exists_finiteOne_strong_picture
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (e : Ordered3Graph.Embedding A.toOrdered3Graph H.toOrdered3Graph)
    (haux : e.AuxTypeRespecting)
    (n : Nat) (hnm : n ≤ m) (hm : 0 < m)
    (hfix : ∀ k < n, e k = k) :
    ∃ r : CoordNode, ∃ S : Set CoordNode,
      (∀ x, finiteOneCandidate A H e n x → x ∈ S) ∧
      CoordNode.FiniteStrongPicture S e (m - 1) r := by
  let E : Set CoordNode := {x | finiteOneCandidate A H e n x}
  have hE : CoordNode.MeetClosed E := by
    intro x y hx hy
    exact A.finiteOneCandidate_meet H e haux n hfix x y hx hy
  obtain ⟨r, hrootLevel, hroot⟩ :
      ∃ r : CoordNode, CoordNode.level r = e 0 ∧
        ∀ x ∈ E, r ≤ x := by
    by_cases hz : n = 0
    · subst n
      obtain ⟨r, _, hlev, hbelow⟩ :=
        A.finiteOneCandidate_root_zero H e haux hm
      exact ⟨r, hlev, fun x hx => hbelow x hx⟩
    · have hn : 0 < n := by omega
      obtain ⟨r, _, hlev, hbelow⟩ :=
        A.finiteOneCandidate_root_positive H e n hn
      have h0 : e 0 = 0 := hfix 0 hn
      exact ⟨r, by rw [h0]; exact hlev, fun x hx => hbelow x hx⟩
  have hlevels :
      ∀ x ∈ E, ∃ i : Nat, i ≤ m - 1 ∧ CoordNode.level x = e i := by
    intro x hx
    obtain ⟨i, him, hi⟩ :=
      A.finiteOneCandidate_levels H e n hnm hfix x hx
    exact ⟨i, by omega, hi⟩
  obtain ⟨S, hES, hstrong⟩ :=
    CoordNode.exists_finite_strong_completion E hE
      e e.strictMono (m - 1) hlevels r hrootLevel hroot
  exact ⟨r, S, fun x hx => hES hx, hstrong⟩

end EnumNode
end ThreeUniformDiaries
