import ThreeUniformDiaries.FiniteStrongBranchExtension
import ThreeUniformDiaries.CanonicalInfiniteAuxEmbedding
import ThreeUniformDiaries.CanonicalInfiniteBranchFactorization
import ThreeUniformDiaries.FiniteAuxBranchEmbedding
import ThreeUniformDiaries.CanonicalRelativeFixedLevels

/-!
# Finite F_I branch codes factor through a genuine aux-type-respecting map

The preceding geometric finite-to-infinite extension theorem shows
that a finite F_I canonical branch map is literally the restriction
of a genuine infinite canonical map F.

The checked infinite canonical image construction provides an
enumerated hypergraph H = imageGraph F A and an honest induced,
aux-type-respecting embedding e : A -> H with vertex map F.level.

We now prove that the ENTIRE finite branch code F_I^S o g_A agrees
literally with g_H o e at every source vertex, and that the fixed
initial hypergraph I is preserved. This is the missing forward
well-definedness half of the manuscript's finite-colouring definition:
there is no assumption that mere membership in the relative K_I
carrier implies an aux-type-respecting embedding.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Every genuine finite synchronized three-coordinate strong picture
acts on the full finite source branch as an actual aux-type-respecting
induced embedding into a countable hypergraph with the prescribed
initial segment. Its source g_A code is literally the canonical
finite branch image, not merely an abstractly isomorphic tuple. -/
theorem exists_finiteStrong_branch_auxTypeFactorization
    {S₀ S₁ S₂ : Set CoordNode}
    {sigma : Nat → Nat} {k n : Nat}
    {r₀ : EnumNode (sigma 0)}
    {r₁ : OneNode (sigma 0)}
    {r₂ : AuxNode (sigma 0)}
    (hS₀ : FiniteStrongPicture S₀ sigma k (.enum (sigma 0) r₀))
    (hS₁ : FiniteStrongPicture S₁ sigma k (.one (sigma 0) r₁))
    (hS₂ : FiniteStrongPicture S₂ sigma k (.aux (sigma 0) r₂))
    (hsigma : StrictMono sigma)
    (A : EnumNode (k + 1))
    (I : EnumNode n) (hI : A.truncate n = I)
    (hfix : ∀ j < n, sigma j = j) :
    ∃ (H : Ordered3Graph Nat)
      (e : Ordered3Graph.Embedding A.toOrdered3Graph H),
      H.initialSegment n = I ∧
      e.AuxTypeRespecting ∧
      (∀ i : Nat, e i = sigma i) ∧
      ∀ i : Fin (k + 1),
        finiteStrongPicture_branchMap hS₀ hS₁ hS₂
            (A.toOrdered3Graph.branchNode i.val)
            (Nat.le_of_lt_succ i.isLt) =
          H.branchNode (e i.val) := by
  obtain ⟨U₀, U₁, U₂, hU₀, hU₁, hU₂,
      hSU₀, hSU₁, hSU₂, hFinite⟩ :=
    exists_infinite_extension_with_branchMap_eq
      hS₀ hS₁ hS₂ hsigma
  let F : CanonicalMap :=
    infiniteStrongPictureCanonicalMap hU₀ hU₁ hU₂ hsigma
  let H : Ordered3Graph Nat := F.imageGraph A.toOrdered3Graph
  let e : Ordered3Graph.Embedding A.toOrdered3Graph H :=
    F.imageGraph_embedding A.toOrdered3Graph
  have hA : A.toOrdered3Graph.initialSegment n = I :=
    (A.toOrdered3Graph_initialSegment n).trans hI
  have hfixF : ∀ j < n, F.level j = j := by
    intro j hj
    exact hfix j hj
  refine ⟨H, e, ?_, ?_, ?_, ?_⟩
  · exact F.imageGraph_initialCut A.toOrdered3Graph I hA
      (F.fixesRelativeCut_of_fixed_levels I hfixF)
  · exact F.imageGraph_auxTypeRespecting A.toOrdered3Graph
  · intro j
    rfl
  · intro i
    calc
      finiteStrongPicture_branchMap hS₀ hS₁ hS₂
          (A.toOrdered3Graph.branchNode i.val)
          (Nat.le_of_lt_succ i.isLt) =
        F.mapBranch (A.toOrdered3Graph.branchNode i.val) :=
        hFinite _ (Nat.le_of_lt_succ i.isLt)
      _ = H.branchNode (e i.val) := by
        exact F.mapBranch_branchNode A.toOrdered3Graph i.val

end CoordNode
end ThreeUniformDiaries
