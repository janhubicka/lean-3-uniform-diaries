import ThreeUniformDiaries.FiniteAembCodingExistence
import ThreeUniformDiaries.FiniteTargetReduction
import ThreeUniformDiaries.InfinitePrefixes

/-!
# Exact finite Aemb canonical coding into any countable enumerated target

The finite converse in the manuscript allows the target H to be an
arbitrary countable enumerated hypergraph. Every actual type or edge
test of a finite source embedding is below the last selected target
vertex. Restrict to N=f(m-1)+1, invoke the genuine finite Aemb
coding-existence theorem, and replace its finite-target truncations
by actual target prefixes.

Thus under precisely the genuine FiniteAuxEmbedding hypotheses and
fixed prefix n, one obtains three typed finite strong coordinate
pictures whose recursively constructed code at every source vertex i
equals G.initialSegment (f i+1) literally.

This theorem is the countable-target finite encoding of manuscript
Lemma Aemb in the explicit EnumNode / CoordNode representation; the
remaining interface is the dictionary with the original K_I
branch hypergraph and its canonical F_I^S maps.
-/

namespace ThreeUniformDiaries
namespace EnumNode

theorem exists_countableAemb_coding
    {m : Nat} (A : EnumNode m) (G : Ordered3Graph Nat)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph G f m)
    (n : Nat) (hnm : n ≤ m) (hm : 0 < m)
    (hfix : ∀ j < n, f j = j) :
    ∃ N : Nat, f (m - 1) < N ∧
      ∃ (r₀ : EnumNode (f 0)) (r₁ : OneNode (f 0))
        (r₂ : AuxNode (f 0)),
      ∃ (S₀ S₁ S₂ : Set CoordNode),
      ∃ (h₀ : CoordNode.FiniteStrongPicture S₀ f (m - 1)
        (.enum (f 0) r₀))
        (h₁ : CoordNode.FiniteStrongPicture S₁ f (m - 1)
          (.one (f 0) r₁))
        (h₂ : CoordNode.FiniteStrongPicture S₂ f (m - 1)
          (.aux (f 0) r₂)),
      ∀ (i : Nat) (him : i < m),
        (CoordNode.finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i
          (by omega) (A.truncate i)).val.succ
          (CoordNode.finiteStrongPicture_oneCanonicalMap h₁ h₂ i
            (by omega) (A.oneType i i)).val =
          G.initialSegment (f i + 1) := by
  let N := f (m - 1) + 1
  have hN : f (m - 1) < N := Nat.lt_succ_self _
  have hfinite :
      Ordered3Graph.FiniteAuxEmbedding A.toOrdered3Graph
        (G.initialSegment N).toOrdered3Graph f m :=
    Ordered3Graph.FiniteAuxEmbedding.target_initialSegment
      A G f hf hm N hN
  obtain ⟨r₀, r₁, r₂, S₀, S₁, S₂,
      h₀, h₁, h₂, _, _, _, hCode⟩ :=
    A.exists_finiteAemb_coding_of_finite
      (G.initialSegment N) f hfinite n hnm hm hfix
  refine ⟨N, hN, r₀, r₁, r₂, S₀, S₁, S₂, h₀, h₁, h₂, ?_⟩
  intro i him
  have hi : i ≤ m - 1 := by omega
  have hfi : f i ≤ f (m - 1) := hf.strictMono.monotone hi
  have hcut : f i + 1 ≤ N := by dsimp [N]; omega
  have hc := hCode i him
  rw [G.initialSegment_truncate hcut] at hc
  exact hc

end EnumNode
end ThreeUniformDiaries
