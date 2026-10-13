import ThreeUniformDiaries.ScalarFiniteColourCode
import ThreeUniformDiaries.ATRBoundaryMillikenApplication

/-!
# The actual finite ATR colouring consequence of heterogeneous Milliken

The manuscript colours genuine embeddings of a FINITE hypergraph A,
not arbitrary zero-extensions of A on Nat, and not artificial tuples
of K_I vertices. The concrete finite scalar decoder now produces a
unique `FiniteAuxEmbeddingImage` with precisely these finite images,
using the same fixed universal K_I embedding for every scalar code.

Here we apply the conditional heterogeneous boundary-product
Halpern--Läuchli / scalar Milliken consequence to that literal finite
colour. Every finite approximation on the protected root-glued
identity stem has a valid decoder value, and its image code is unique.

This closes the finite-colouring portion of the ATR Ramsey argument
WITHOUT an abstract `ATRScalarRealization` assumption. The strong
refinement of an arbitrary finite source code and the final ambient
self-embedding are the next distinct steps.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree
open ThreeUniformDiaries.CoordNode
open ThreeUniformDiaries.ATRGeneralMilliken

/-- The literal finite scalar colouring on ALL published finite
Milliken approximations, with a harmless default outside the
protected identity-stem neighbourhood. -/
noncomputable def actualScalarFiniteColour
    (G : GenericEnumerated3Graph)
    {k n : Nat} (hnk : n ≤ k + 1)
    (A : EnumNode (k + 1))
    (I : EnumNode n) (hI : A.truncate n = I)
    (E : SizeFirstBranchPresentation I)
    (phi : Nat → Nat)
    (hphi : UniversalAuxBranchProperty G I E phi)
    {κ : Type} [Nonempty κ]
    (χ : Ordered3Graph.FiniteAuxEmbeddingImage
      A.toOrdered3Graph G.graph (k + 1) → κ)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2)) : κ :=
  match scalarFiniteColourCode G hnk A I hI E phi hphi a with
  | none => Classical.choice inferInstance
  | some c => χ c

/-- The genuine fixed-stem finite-colour ATR theorem on the REAL
heterogeneous scalar root-glued E0/E1/E2 tree. The only unproved
input is precisely the upstream heterogeneous boundary-product HL
property, passed visibly as a hypothesis.

For every strong refinement X of B with the full first n+1 scalar
levels protected, every finite embedding code represented by its
height-(k+2) scalar approximation receives the same χ-colour.
The code is a genuine Fin(k+1)-vertex aux embedding of A in G. -/
theorem actualScalarFiniteColour_monochromatic
    (G : GenericEnumerated3Graph)
    {k n : Nat} (hnk : n ≤ k + 1)
    (A : EnumNode (k + 1))
    (I : EnumNode n) (hI : A.truncate n = I)
    (E : SizeFirstBranchPresentation I)
    (phi : Nat → Nat)
    (hphi : UniversalAuxBranchProperty G I E phi)
    (hHL : Milliken.GeneralTree.HasBoundaryProductHL
      CoordNode.rootGluedAmbientTree)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : Ordered3Graph.FiniteAuxEmbeddingImage
      A.toOrdered3Graph G.graph (k + 1) → κ) :
    ∃ B : StrongSubtree CoordNode.rootGluedAmbientTree,
      B.Refines scalarIdentity ∧
      r (n + 1) B = r (n + 1) scalarIdentity ∧
      ∃ color : κ,
        ∀ (X : StrongSubtree CoordNode.rootGluedAmbientTree),
          X.Refines B →
          r (n + 1) X = r (n + 1) scalarIdentity →
          ∀ code : Ordered3Graph.FiniteAuxEmbeddingImage
              A.toOrdered3Graph G.graph (k + 1),
            ScalarFiniteImageEquation G A I E phi
              (r (k + 2) X)
              (protectedScalarApprox_root_mem k n
                (r (k + 2) X)
                ⟨X, rfl, by assumption⟩) code →
            χ code = color := by
  let col := actualScalarFiniteColour G hnk A I hI E phi hphi χ
  obtain ⟨B, hBA, hstemB, hhom⟩ :=
    anchoredFiniteColour_of_boundaryProductHL
      CoordNode.rootGluedAmbientTree hHL
      (n + 1) (k + 2) scalarIdentity col
  refine ⟨B, hBA, hstemB, col (r (k + 2) B), ?_⟩
  intro X hXB hstemX code hcode
  have hvalid : ∃ T : StrongSubtree CoordNode.rootGluedAmbientTree,
      r (k + 2) T = r (k + 2) X ∧
      r (n + 1) T = r (n + 1) scalarIdentity :=
    ⟨X, rfl, hstemX⟩
  obtain ⟨codeX, hcodeX, hspecX⟩ :=
    scalarFiniteColourCode_some
      G hnk A I hI E phi hphi (r (k + 2) X) hvalid
  have hsame : code = codeX :=
    (existsUnique_scalarFiniteImage
      G hnk A I hI E phi hphi (r (k + 2) X)
      hvalid).unique hcode hspecX
  have hcol : col (r (k + 2) X) = χ code := by
    change (match scalarFiniteColourCode G hnk A I hI E phi hphi
      (r (k + 2) X) with
      | none => Classical.choice inferInstance
      | some c => χ c) = χ code
    rw [hcodeX]
    simpa only [hsame]
  have heq :=
    hhom X B hXB (StrongSubtree.refines_refl B) hstemX hstemB
  exact hcol.symm.trans heq

end ATRFiniteDecoder
end ThreeUniformDiaries
