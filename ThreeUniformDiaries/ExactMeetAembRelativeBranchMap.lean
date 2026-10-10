import ThreeUniformDiaries.CountableAembRelativeBranch
import ThreeUniformDiaries.FiniteCanonicalBranchMap
import ThreeUniformDiaries.FiniteExactMeetInterface

/-!
# The finite converse on the actual relative K_I branches

The hypothesis is now *literally* the manuscript's finite
aux-type-respecting embedding: induced triples and exact capped
singleton / auxiliary meet preservation on the true finite source.
No stronger selected-cut or artificial infinite-source property is
assumed; the exact-meet interface equivalence supplies the bridge.

For I=A|n=G|n, construct a synchronized finite strong vector picture
whose concrete finite F^S map is defined for ALL universal branch
vertices of source height <=m, and prove its equality with g_G ∘ f
on every vertex of the finite source branch g_A[A].

This is the finite converse's full branch equality in the explicit
RelativeBranchNode presentation, as distinct from the independent
infinite canonical-map and vector Milliken assertions.
-/

namespace ThreeUniformDiaries
namespace EnumNode

theorem exists_exactMeetAemb_relativeBranchMap
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
      ∀ (i : Nat) (him : i < m),
        CoordNode.finiteStrongPicture_branchMap h₀ h₁ h₂
          (A.toOrdered3Graph.relativeBranchNode I hA i).val
          (by change i ≤ m - 1; omega) =
          (G.relativeBranchNode I hG (f i)).val := by
  obtain ⟨N, hN, r₀, r₁, r₂, S₀, S₁, S₂,
      h₀, h₁, h₂, hCodes⟩ :=
    A.exists_countableAemb_relativeBranch_coding
      G I hG f hf.toFiniteAuxEmbedding hnm hm hfix
  refine ⟨r₀, r₁, r₂, S₀, S₁, S₂, h₀, h₁, h₂, ?_⟩
  intro i him
  change CoordNode.finiteStrongPicture_branchMap h₀ h₁ h₂
      (A.toOrdered3Graph.branchNode i)
      (by change i ≤ m - 1; omega) =
      (G.relativeBranchNode I hG (f i)).val
  calc
    CoordNode.finiteStrongPicture_branchMap h₀ h₁ h₂
        (A.toOrdered3Graph.branchNode i)
        (by change i ≤ m - 1; omega) =
      (⟨f i,
        (CoordNode.finiteStrongPicture_enumCanonicalMap
          h₀ h₁ h₂ i (by omega) (A.truncate i)).val.succ
        (CoordNode.finiteStrongPicture_oneCanonicalMap
          h₁ h₂ i (by omega) (A.oneType i i)).val⟩ :
        EnumerationBranchNode) :=
      CoordNode.finiteStrongPicture_branchMap_source
        A h₀ h₁ h₂ i (by omega)
    _ = (G.relativeBranchNode I hG (f i)).val :=
      hCodes i him

end EnumNode
end ThreeUniformDiaries
