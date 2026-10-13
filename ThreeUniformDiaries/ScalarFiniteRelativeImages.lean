import ThreeUniformDiaries.ScalarProtectedRelativeDecode
import ThreeUniformDiaries.FiniteAuxBranchEmbedding

/-!
# The real finite K_I image tuple decoded from a scalar Milliken approximation

For a prescribed finite enumerated hypergraph A of height k+1, its
canonical universal K_I branch is the actual list of relative branch
vertices g_A(i), i≤k. The independent scalar finite-code decoder
is now a total function on these indexed vertices with Option output.

On any height-(k+2) scalar finite approximation with the protected
identity stem, all outputs succeed and assemble into an honest finite
tuple of K_I vertices. This is the concrete finite data which is to
be coloured after composing with the fixed universal K_I embedding.

The remaining mathematical issue before applying the colouring is
to prove that this assembled tuple preserves and reflects the exact
induced triples and capped type meets; its mere carrier membership
does not yet imply aux-type-respecting embedding.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree
open ThreeUniformDiaries.CoordNode

/-- The actual i-th source branch vertex of the finite hypergraph A
in the relative universal K_I tree, with its source prefix proof. -/
noncomputable def finiteSourceRelativeBranch
    {k n : Nat} (A : EnumNode (k + 1))
    (I : EnumNode n) (hI : A.truncate n = I)
    (i : Fin (k + 1)) : RelativeBranchNode I :=
  A.toOrdered3Graph.relativeBranchNode I
    ((EnumNode.toOrdered3Graph_initialSegment A n).trans hI)
    i.val

/-- The image of all k+1 source branch vertices under the genuine
scalar finite F_I decoder. Values are determined entirely by the
finite scalar approximation, not its chosen infinite realizer. -/
noncomputable def finiteScalarRelativeImages
    {k n : Nat} (A : EnumNode (k + 1))
    (I : EnumNode n) (hI : A.truncate n = I)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2)) :
    Fin (k + 1) → Option (RelativeBranchNode I) :=
  fun i =>
    decodeFiniteRelativeBranch k n I a
      (finiteSourceRelativeBranch A I hI i)
      (Nat.le_of_lt_succ i.isLt)

/-- The protected scalar stem makes the genuine F_I finite code
successful on EVERY actual source branch vertex. -/
theorem finiteScalarRelativeImages_all_some
    {k n : Nat} (A : EnumNode (k + 1))
    (I : EnumNode n) (hI : A.truncate n = I)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (hn : n ≤ k + 1)
    (hvalid : ∃ S : StrongSubtree CoordNode.rootGluedAmbientTree,
      r (k + 2) S = a ∧
      r (n + 1) S = r (n + 1) scalarIdentity) :
    ∀ i : Fin (k + 1),
      ∃ b : RelativeBranchNode I,
        finiteScalarRelativeImages A I hI a i = some b := by
  intro i
  exact protectedScalar_decodeFiniteRelativeBranch_some k n
    a hn hvalid I
    (finiteSourceRelativeBranch A I hI i)
    (Nat.le_of_lt_succ i.isLt)

/-- Package the successful decoder outputs into an ACTUAL tuple of
K_I vertices, whose equality to the scalar finite code is checked
at each source index. No arbitrary fallback colours survive. -/
theorem exists_finiteScalarRelativeImage_tuple
    {k n : Nat} (A : EnumNode (k + 1))
    (I : EnumNode n) (hI : A.truncate n = I)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (hn : n ≤ k + 1)
    (hvalid : ∃ S : StrongSubtree CoordNode.rootGluedAmbientTree,
      r (k + 2) S = a ∧
      r (n + 1) S = r (n + 1) scalarIdentity) :
    ∃ e : Fin (k + 1) → RelativeBranchNode I,
      ∀ i : Fin (k + 1),
        finiteScalarRelativeImages A I hI a i = some (e i) := by
  classical
  let hex := finiteScalarRelativeImages_all_some A I hI a hn hvalid
  refine ⟨fun i => Classical.choose (hex i), ?_⟩
  intro i
  exact Classical.choose_spec (hex i)

end ATRFiniteDecoder
end ThreeUniformDiaries
