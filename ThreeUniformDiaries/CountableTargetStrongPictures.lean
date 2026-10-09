import ThreeUniformDiaries.FiniteTargetReduction
import ThreeUniformDiaries.ActualFiniteCoordinateCompletion

/-!
# The finite strong-tree picture inside an arbitrary countable target

Aemb starts with an arbitrary enumerated hypergraph G on Nat, rather
than a finite target EnumNode N. Choose the finite initial segment
ending just after the last selected image of the m actual source
vertices. All selected-cut tests occur within it.

The checked finite target reduction transports the real finite
embedding conditions to that prefix. We then apply the verified
three-coordinate strong-completion theorem. No genericity or
assumption on artificially extended source vertices is needed.
-/

namespace ThreeUniformDiaries
namespace EnumNode

/-- The entire structural strong-tree part of the finite converse,
with a genuinely finite embedding of A into any countable target G:
one finite target prefix suffices for constructing the synchronized
coordinate pictures at the selected levels. -/
theorem exists_threeCoordinate_pictures_countable_target
    {m : Nat} (A : EnumNode m) (G : Ordered3Graph Nat)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph G f m)
    (n : Nat) (hnm : n ≤ m) (hm : 0 < m)
    (hfix : ∀ k < n, f k = k) :
    ∃ N : Nat, f (m - 1) < N ∧
      ∃ r₀ r₁ r₂ : CoordNode,
      ∃ S₀ S₁ S₂ : Set CoordNode,
      (∀ x, finiteEnumCandidate (G.initialSegment N)
        f n m x → x ∈ S₀) ∧
      (∀ x, finiteOneCandidate A (G.initialSegment N)
        f n x → x ∈ S₁) ∧
      (∀ x, finiteAuxCandidate A (G.initialSegment N)
        f n x → x ∈ S₂) ∧
      CoordNode.FiniteStrongPicture S₀ f (m - 1) r₀ ∧
      CoordNode.FiniteStrongPicture S₁ f (m - 1) r₁ ∧
      CoordNode.FiniteStrongPicture S₂ f (m - 1) r₂ := by
  let N := f (m - 1) + 1
  have hN : f (m - 1) < N := Nat.lt_succ_self _
  have hfinite :
      Ordered3Graph.FiniteAuxEmbedding A.toOrdered3Graph
        (G.initialSegment N).toOrdered3Graph f m :=
    Ordered3Graph.FiniteAuxEmbedding.target_initialSegment
      A G f hf hm N hN
  obtain ⟨r₀, r₁, r₂, S₀, S₁, S₂,
      hS₀, hS₁, hS₂, hstrong₀, hstrong₁, hstrong₂⟩ :=
    A.exists_threeCoordinate_picture_of_finite
      (G.initialSegment N) f hfinite n hnm hm hfix
  exact ⟨N, hN, r₀, r₁, r₂, S₀, S₁, S₂,
    hS₀, hS₁, hS₂, hstrong₀, hstrong₁, hstrong₂⟩

end EnumNode
end ThreeUniformDiaries
