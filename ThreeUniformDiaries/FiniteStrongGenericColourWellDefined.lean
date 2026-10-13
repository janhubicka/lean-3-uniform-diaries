import ThreeUniformDiaries.FiniteStrongBranchFactorization
import ThreeUniformDiaries.AuxTypeRespectingComposition
import ThreeUniformDiaries.UniversalAuxBranchEmbedding

/-!
# The finite ATR colour is a genuine aux-type-respecting embedding

The manuscript colours finite strong vectors S by the actual map
phi o F_I^S o g_A.  Membership of every F_I^S(g_A(i)) in K_I is
not by itself sufficient to show that this is an aux-type-respecting
embedding. We instead use the checked finite geometric factorisation:

  F_I^S o g_A = g_H o e_A,

where H is an actual countable canonical image of A, e_A is induced
and preserves/refects all singleton and auxiliary type tests, and H
has the fixed initial hypergraph I.

The single UNIFORM K_I embedding, chosen once for G and I, then
provides an embedding e_G:H->G compatible with the SAME phi used
for all finite codes. Their composition is genuinely induced and
aux-type-respecting, preserves the original fixed n vertices, and
its vertex map is the intended phi o F_I^S o g_A index formula.

The heterogeneous Milliken theorem is not used in this lemma.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Given the single preselected universal K_I embedding E,phi,
EVERY finite synchronized strong picture produces a real
aux-type-respecting embedding into the generic hypergraph. The
finite F_I branch images are the literal branch nodes of the
intermediate canonical image H, and the final vertex map is exactly
the uniform phi applied to their K_I length-first indices. -/
theorem exists_finiteStrong_actualAuxEmbedding_to_generic
    (G : GenericEnumerated3Graph)
    {k n : Nat}
    (I : EnumNode n)
    (E : SizeFirstBranchPresentation I)
    (phi : Nat → Nat)
    (hphi : UniversalAuxBranchProperty G I E phi)
    {S₀ S₁ S₂ : Set CoordNode}
    {sigma : Nat → Nat}
    {r₀ : EnumNode (sigma 0)}
    {r₁ : OneNode (sigma 0)}
    {r₂ : AuxNode (sigma 0)}
    (hS₀ : FiniteStrongPicture S₀ sigma k (.enum (sigma 0) r₀))
    (hS₁ : FiniteStrongPicture S₁ sigma k (.one (sigma 0) r₁))
    (hS₂ : FiniteStrongPicture S₂ sigma k (.aux (sigma 0) r₂))
    (hsigma : StrictMono sigma)
    (A : EnumNode (k + 1))
    (hI : A.truncate n = I)
    (hfix : ∀ j < n, sigma j = j) :
    ∃ (H : Ordered3Graph Nat)
      (hH : H.initialSegment n = I)
      (eA : Ordered3Graph.Embedding A.toOrdered3Graph H)
      (eG : Ordered3Graph.Embedding H G.graph),
      eA.AuxTypeRespecting ∧
      eG.AuxTypeRespecting ∧
      (eG.comp eA).AuxTypeRespecting ∧
      (∀ j : Nat, j < n → (eG.comp eA) j = j) ∧
      (∀ i : Fin (k + 1),
        finiteStrongPicture_branchMap hS₀ hS₁ hS₂
            (A.toOrdered3Graph.branchNode i.val)
            (Nat.le_of_lt_succ i.isLt) =
          H.branchNode (eA i.val)) ∧
      (∀ i : Fin (k + 1),
        (eG.comp eA) i.val =
          phi (E.branchIndex H hH (sigma i.val))) := by
  obtain ⟨H, eA, hH, hauxA, hlevelA, hbranch⟩ :=
    exists_finiteStrong_branch_auxTypeFactorization
      hS₀ hS₁ hS₂ hsigma A I hI hfix
  obtain ⟨eG, hmap, hfixG, hauxG⟩ :=
    hphi.2.2.2 H hH
  have hauxComposite : (eG.comp eA).AuxTypeRespecting :=
    hauxG.comp hauxA
  have hfixA : ∀ j : Nat, j < n → eA j = j := by
    intro j hj
    exact (hlevelA j).trans (hfix j hj)
  have hfixComposite : ∀ j : Nat, j < n →
      (eG.comp eA) j = j :=
    Ordered3Graph.Embedding.comp_fixed_prefix eG eA n
      hfixA hfixG
  refine ⟨H, hH, eA, eG,
    hauxA, hauxG, hauxComposite,
    hfixComposite, hbranch, ?_⟩
  intro i
  calc
    (eG.comp eA) i.val = eG (eA i.val) := rfl
    _ = eG (sigma i.val) := by rw [hlevelA i.val]
    _ = phi (E.branchIndex H hH (sigma i.val)) :=
      hmap (sigma i.val)

end CoordNode
end ThreeUniformDiaries
