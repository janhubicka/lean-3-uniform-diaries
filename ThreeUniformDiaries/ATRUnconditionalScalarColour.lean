import ThreeUniformDiaries.ScalarActualFiniteMillikenColour
import Milliken.GeneralTree.UnconditionalHLAPI
import Milliken.GeneralTree.FixedStemUnconditional

/-!
# Unconditional arbitrary-branching Milliken in the concrete ATR colouring

The upstream lean-milliken library has now proved the universal
heterogeneous HDHL induction and the unrestricted general-tree
Milliken theorem, with no bound on the locally finite branching
degree. In particular, its theorem boundaryProductHL_unconditional
discharges the last external combinatorial input of the concrete
root-glued E0/E1/E2 scalar finite-colouring proof.

The theorem below is not a conditional consequence with a named
HL assumption. It is the genuine unconditional anchored
monochromaticity of the finite ATR scalar colour on the REAL
nonhomogeneous scalar tree.

The final ATR arrow theorem additionally uses a concrete finite
image realization/decoder congruence, developed separately.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree
open ThreeUniformDiaries.CoordNode

/-- Actual finite ATR scalar colour is monochromatic on a protected
nonuniformly branching strong subtree, without any remaining
Halpern–Läuchli or Milliken theorem hypothesis. -/
theorem actualScalarFiniteColour_monochromatic_unconditional
    (G : GenericEnumerated3Graph)
    {k n : Nat} (hnk : n ≤ k + 1)
    (A : EnumNode (k + 1))
    (I : EnumNode n) (hI : A.truncate n = I)
    (E : SizeFirstBranchPresentation I)
    (phi : Nat → Nat)
    (hphi : UniversalAuxBranchProperty G I E phi)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : Ordered3Graph.FiniteAuxEmbeddingImage
      A.toOrdered3Graph G.graph (k + 1) → κ) :
    ∃ B : StrongSubtree CoordNode.rootGluedAmbientTree,
      B.Refines scalarIdentity ∧
      r (n + 1) B = r (n + 1) scalarIdentity ∧
      ∃ color : κ,
        ∀ (X : StrongSubtree CoordNode.rootGluedAmbientTree),
          X.Refines B →
          ∀ hstemX : r (n + 1) X = r (n + 1) scalarIdentity,
          ∀ code : Ordered3Graph.FiniteAuxEmbeddingImage
              A.toOrdered3Graph G.graph (k + 1),
            ScalarFiniteImageEquation G A I E phi
              (r (k + 2) X)
              (protectedScalarApprox_root_mem k n
                (r (k + 2) X)
                ⟨X, rfl, hstemX⟩) code →
            χ code = color := by
  exact actualScalarFiniteColour_monochromatic
    G hnk A I hI E phi hphi
    (Milliken.GeneralTree.boundaryProductHL_unconditional
      CoordNode.rootGluedAmbientTree) χ

end ATRFiniteDecoder
end ThreeUniformDiaries
