import ThreeUniformDiaries.FiniteRelativeCarrier
import ThreeUniformDiaries.ExactMeetAembFullPrefix

/-!
# The complete finite converse with a well-defined relative K_I map

Assume the exact capped-meet formulation of a genuine finite
aux-type-respecting embedding A -> G fixing an initial enumeration I.

The synchronized finite strong pictures produced by the verified
finite converse contain every node at the first n levels. Their
constructed canonical branch map is well-defined on the *entire*
relative carrier K_I of source height <=m, not only g_A[A].

On every actual vertex i of A this map is literally g_G(f(i)).
The proof combines full first-n-level preservation and relative
carrier closure with the checked exact-meet source branch equality.
No assumption on artificial source vertices is needed.

This completes Lemma Aemb in the explicit relative branch and finite
strong-picture representation. It does NOT imply that the independent
infinite canonical-map lemma, composition lemma, or vector Milliken
transfer has been formalized.
-/

namespace ThreeUniformDiaries
namespace EnumNode

theorem exists_exactMeetAemb_full_relative_map
    {m n : Nat} (A : EnumNode m) (G : Ordered3Graph Nat)
    (I : EnumNode n)
    (hA : A.toOrdered3Graph.initialSegment n = I)
    (hG : G.initialSegment n = I)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteExactMeetEmbedding
      A.toOrdered3Graph G f m)
    (hnm : n ≤ m) (hm : 0 < m)
    (hfix : ∀ j < n, f j = j) :
    ∃ (r₀ : EnumNode (f 0)) (r₁ : OneNode (f 0))
      (r₂ : AuxNode (f 0)),
      ∃ (S₀ S₁ S₂ : Set CoordNode),
      ∃ (h₀ : CoordNode.FiniteStrongPicture S₀ f (m - 1)
        (.enum (f 0) r₀))
        (h₁ : CoordNode.FiniteStrongPicture S₁ f (m - 1)
          (.one (f 0) r₁))
        (h₂ : CoordNode.FiniteStrongPicture S₂ f (m - 1)
          (.aux (f 0) r₂)),
      ∃ (hfull₀ : ∀ (j : Nat) (hj : j < n)
        (B : EnumNode j), CoordNode.enum j B ∈ S₀)
        (hfull₁ : ∀ (j : Nat) (hj : j < n)
          (B : OneNode j), CoordNode.one j B ∈ S₁)
        (hfull₂ : ∀ (j : Nat) (hj : j < n)
          (B : AuxNode j), CoordNode.aux j B ∈ S₂),
      ∀ (i : Nat) (him : i < m),
        CoordNode.finiteRelativeBranchMap
          h₀ h₁ h₂ hf.strictMono hfix
          (by omega) (hfull₀ 0) (hfull₁ 0) (hfull₂ 0)
          I (A.toOrdered3Graph.relativeBranchNode I hA i)
          (by change i ≤ m - 1; omega) =
            G.relativeBranchNode I hG (f i) := by
  obtain ⟨r₀, r₁, r₂, S₀, S₁, S₂,
      h₀, h₁, h₂, hfull₀, hfull₁, hfull₂, hcode⟩ :=
    A.exists_exactMeetAemb_fullPrefix_branchMap
      G I hA hG f hf hnm hm hfix
  refine ⟨r₀, r₁, r₂, S₀, S₁, S₂,
    h₀, h₁, h₂, hfull₀, hfull₁, hfull₂, ?_⟩
  intro i him
  apply Subtype.ext
  exact hcode i him

end EnumNode
end ThreeUniformDiaries
