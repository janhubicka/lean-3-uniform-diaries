import ThreeUniformDiaries.FiniteAuxEmbeddingImage
import ThreeUniformDiaries.ScalarFiniteGenericColour

/-!
# An actual finite ATR colour, independent of all coding witnesses

The scalar Milliken colouring must assign a colour to each finite
strong-tree approximation, not to a chosen infinite extension or
a chosen sequence of roots. The true finite image of A in G is
uniquely determined by the finite F_I action and the ONE fixed
universal K_I embedding phi.

We prove both existence and uniqueness in the genuinely finite
Fin(m)-vertex aux-type embedding domain. The colour is therefore
well-defined even if different admissible infinite extensions of
the finite picture yield different values above the last source
vertex. Rootedness, selected heights and all E0/E1/E2 canonical
maps have already been proved independent of such choices.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree
open ThreeUniformDiaries.CoordNode

/-- The exact pointwise equation defining the finite colour of a
scalar approximation: phi composed with the actual canonical
finite F_I(g_A(i)) branch index, for every genuine source vertex. -/
def ScalarFiniteImageEquation
    (G : GenericEnumerated3Graph)
    {k n : Nat}
    (A : EnumNode (k + 1)) (I : EnumNode n)
    (E : SizeFirstBranchPresentation I) (phi : Nat → Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (hroot : (none : WithBot CoordNode) ∈ a.carrier)
    (c : Ordered3Graph.FiniteAuxEmbeddingImage
      A.toOrdered3Graph G.graph (k + 1)) : Prop :=
  ∀ i : Fin (k + 1),
    ∃ hB : InRelativeBranchGraph I
      (rootedScalarFiniteBranchMap k a hroot
        (A.toOrdered3Graph.branchNode i.val)
        (Nat.le_of_lt_succ i.isLt)),
      c.image i =
        phi (E.code.symm
          (⟨rootedScalarFiniteBranchMap k a hroot
              (A.toOrdered3Graph.branchNode i.val)
              (Nat.le_of_lt_succ i.isLt), hB⟩ :
            RelativeBranchNode I))

/-- There is EXACTLY ONE genuine finite aux-type embedding image
obeying the manuscript's scalar F_I colouring formula on a
protected finite approximation. Existence comes from the uniform
K_I induced embedding theorem; uniqueness comes from finite-vertex
extensionality and proof irrelevance for the K_I carrier predicate. -/
theorem existsUnique_scalarFiniteImage
    (G : GenericEnumerated3Graph)
    {k n : Nat} (hnk : n ≤ k + 1)
    (A : EnumNode (k + 1))
    (I : EnumNode n) (hI : A.truncate n = I)
    (E : SizeFirstBranchPresentation I)
    (phi : Nat → Nat)
    (hphi : UniversalAuxBranchProperty G I E phi)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (hvalid : ∃ S : StrongSubtree CoordNode.rootGluedAmbientTree,
      r (k + 2) S = a ∧
      r (n + 1) S = r (n + 1) scalarIdentity) :
    ∃! c : Ordered3Graph.FiniteAuxEmbeddingImage
        A.toOrdered3Graph G.graph (k + 1),
      ScalarFiniteImageEquation G A I E phi a
        (protectedScalarApprox_root_mem k n a hvalid) c := by
  obtain ⟨e, he, _, hformula⟩ :=
    exists_scalarFinite_phi_FI_gA_auxEmbedding
      G hnk A I hI E phi hphi a hvalid
  let code : Ordered3Graph.FiniteAuxEmbeddingImage
      A.toOrdered3Graph G.graph (k + 1) :=
    Ordered3Graph.FiniteAuxEmbeddingImage.ofAuxTypeRespectingEmbedding
      e he
  have hcode : ScalarFiniteImageEquation G A I E phi a
      (protectedScalarApprox_root_mem k n a hvalid) code := by
    intro i
    obtain ⟨hB, hval⟩ := hformula i
    exact ⟨hB, hval⟩
  refine ⟨code, hcode, ?_⟩
  intro d hd
  apply Ordered3Graph.FiniteAuxEmbeddingImage.ext d code
  intro i
  obtain ⟨hBd, hvalD⟩ := hd i
  obtain ⟨hBc, hvalC⟩ := hcode i
  calc
    d.image i =
      phi (E.code.symm
        (⟨rootedScalarFiniteBranchMap k a
            (protectedScalarApprox_root_mem k n a hvalid)
            (A.toOrdered3Graph.branchNode i.val)
            (Nat.le_of_lt_succ i.isLt), hBd⟩ :
          RelativeBranchNode I)) := hvalD
    _ = phi (E.code.symm
        (⟨rootedScalarFiniteBranchMap k a
            (protectedScalarApprox_root_mem k n a hvalid)
            (A.toOrdered3Graph.branchNode i.val)
            (Nat.le_of_lt_succ i.isLt), hBc⟩ :
          RelativeBranchNode I)) := by
        congr 1
    _ = code.image i := hvalC.symm

/-- The total Option-valued FINITE colouring code. Invalid scalar
approximations have no protected source code, and valid ones give
the unique genuine aux-type-respecting image of the m real vertices.
No continuation of a finite enumerated hypergraph is colourable
as extra data. -/
noncomputable def scalarFiniteColourCode
    (G : GenericEnumerated3Graph)
    {k n : Nat} (hnk : n ≤ k + 1)
    (A : EnumNode (k + 1))
    (I : EnumNode n) (hI : A.truncate n = I)
    (E : SizeFirstBranchPresentation I)
    (phi : Nat → Nat)
    (hphi : UniversalAuxBranchProperty G I E phi)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2)) :
    Option (Ordered3Graph.FiniteAuxEmbeddingImage
      A.toOrdered3Graph G.graph (k + 1)) := by
  classical
  exact if hvalid : ∃ S : StrongSubtree CoordNode.rootGluedAmbientTree,
      r (k + 2) S = a ∧
      r (n + 1) S = r (n + 1) scalarIdentity then
    some (Classical.choose
      (existsUnique_scalarFiniteImage G hnk A I hI E phi hphi
        a hvalid).exists)
  else none

/-- On actual protected scalar finite approximations the total
finite-colour code never falls back to its invalid branch. -/
theorem scalarFiniteColourCode_some
    (G : GenericEnumerated3Graph)
    {k n : Nat} (hnk : n ≤ k + 1)
    (A : EnumNode (k + 1))
    (I : EnumNode n) (hI : A.truncate n = I)
    (E : SizeFirstBranchPresentation I)
    (phi : Nat → Nat)
    (hphi : UniversalAuxBranchProperty G I E phi)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (hvalid : ∃ S : StrongSubtree CoordNode.rootGluedAmbientTree,
      r (k + 2) S = a ∧
      r (n + 1) S = r (n + 1) scalarIdentity) :
    ∃ c : Ordered3Graph.FiniteAuxEmbeddingImage
        A.toOrdered3Graph G.graph (k + 1),
      scalarFiniteColourCode G hnk A I hI E phi hphi a = some c ∧
      ScalarFiniteImageEquation G A I E phi a
        (protectedScalarApprox_root_mem k n a hvalid) c := by
  classical
  let ex := (existsUnique_scalarFiniteImage G hnk A I hI E phi hphi
    a hvalid).exists
  refine ⟨Classical.choose ex, ?_, Classical.choose_spec ex⟩
  simp [scalarFiniteColourCode, hvalid]

end ATRFiniteDecoder
end ThreeUniformDiaries
