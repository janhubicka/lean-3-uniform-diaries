import ThreeUniformDiaries.FiniteEncoderStrongE0E1

/-!
# Complete the auxiliary-pair coordinate of the finite encoder

The abstract strong-completion theorem is slightly stronger than the
same-level-set observation: one can prescribe any finite increasing
level sequence CONTAINING all levels of E, even if E itself misses
the final level. The generic construction fills it automatically.

Consequently it is unnecessary to append an arbitrary terminal
auxiliary node before completing E2^-; the n=0,m=1 case also
requires no separate terminal extension. We need only choose an
initial root when the candidate E2^- is empty.
-/

namespace ThreeUniformDiaries
namespace EnumNode

/-- E2^- has a strong completion on exactly all m selected levels,
even when its final level is missing. No auxiliary terminal-node
choice is needed with the stronger abstract completion theorem. -/
theorem exists_finiteAux_strong_picture
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (e : Ordered3Graph.Embedding A.toOrdered3Graph H.toOrdered3Graph)
    (haux : e.AuxTypeRespecting)
    (n : Nat) (hnm : n ≤ m) (hm : 0 < m)
    (hfix : ∀ k < n, e k = k) :
    ∃ r : CoordNode, ∃ S : Set CoordNode,
      (∀ x, finiteAuxCandidate A H e n x → x ∈ S) ∧
      CoordNode.FiniteStrongPicture S e (m - 1) r := by
  let E : Set CoordNode := {x | finiteAuxCandidate A H e n x}
  have hE : CoordNode.MeetClosed E := by
    intro x y hx hy
    exact A.finiteAuxCandidate_meet H e haux n hfix x y hx hy
  obtain ⟨r, hrootLevel, hroot⟩ :
      ∃ r : CoordNode, CoordNode.level r = e 0 ∧
        ∀ x ∈ E, r ≤ x := by
    by_cases hz : n = 0
    · subst n
      by_cases hm2 : 1 < m
      · obtain ⟨r, _, hlev, hbelow⟩ :=
          A.finiteAuxCandidate_root_zero H e haux hm2
        exact ⟨r, hlev, fun x hx => hbelow x hx⟩
      · have hm1 : m = 1 := by omega
        subst m
        let r := CoordNode.aux (e 0) (AuxNode.zero (e 0))
        refine ⟨r, rfl, ?_⟩
        intro x hx
        rcases hx with ⟨k, B, hk, hxeq⟩ |
          ⟨i, u₀, u₁, hni, hiu, hu, hum, hxeq⟩
        · omega
        · omega
    · have hn : 0 < n := by omega
      obtain ⟨r, _, hlev, hbelow⟩ :=
        A.finiteAuxCandidate_root_positive H e n hn
      have h0 : e 0 = 0 := hfix 0 hn
      exact ⟨r, by rw [h0]; exact hlev, fun x hx => hbelow x hx⟩
  have hlevels :
      ∀ x ∈ E, ∃ i : Nat, i ≤ m - 1 ∧ CoordNode.level x = e i := by
    intro x hx
    obtain ⟨i, him, hi⟩ :=
      A.finiteAuxCandidate_levels H e n hnm hfix x hx
    exact ⟨i, by omega, hi⟩
  obtain ⟨S, hES, hstrong⟩ :=
    CoordNode.exists_finite_strong_completion E hE
      e e.strictMono (m - 1) hlevels r hrootLevel hroot
  exact ⟨r, S, fun x hx => hES hx, hstrong⟩

/-- All three finite candidate pictures have synchronized strong
completions over the SAME selected level map e; this is the strong
subtree portion of manuscript Lemma Aemb. -/
theorem exists_finite_threeCoordinate_strong_pictures
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (e : Ordered3Graph.Embedding A.toOrdered3Graph H.toOrdered3Graph)
    (haux : e.AuxTypeRespecting)
    (n : Nat) (hnm : n ≤ m) (hm : 0 < m)
    (hfix : ∀ k < n, e k = k) :
    ∃ r₀ r₁ r₂ : CoordNode,
      ∃ S₀ S₁ S₂ : Set CoordNode,
      (∀ x, finiteEnumCandidate H e n m x → x ∈ S₀) ∧
      (∀ x, finiteOneCandidate A H e n x → x ∈ S₁) ∧
      (∀ x, finiteAuxCandidate A H e n x → x ∈ S₂) ∧
      CoordNode.FiniteStrongPicture S₀ e (m - 1) r₀ ∧
      CoordNode.FiniteStrongPicture S₁ e (m - 1) r₁ ∧
      CoordNode.FiniteStrongPicture S₂ e (m - 1) r₂ := by
  obtain ⟨r₀, S₀, hS₀, hstr₀⟩ :=
    A.exists_finiteEnum_strong_picture H e n hnm hm hfix
  obtain ⟨r₁, S₁, hS₁, hstr₁⟩ :=
    A.exists_finiteOne_strong_picture H e haux n hnm hm hfix
  obtain ⟨r₂, S₂, hS₂, hstr₂⟩ :=
    A.exists_finiteAux_strong_picture H e haux n hnm hm hfix
  exact ⟨r₀, r₁, r₂, S₀, S₁, S₂,
    hS₀, hS₁, hS₂, hstr₀, hstr₁, hstr₂⟩

end EnumNode
end ThreeUniformDiaries
