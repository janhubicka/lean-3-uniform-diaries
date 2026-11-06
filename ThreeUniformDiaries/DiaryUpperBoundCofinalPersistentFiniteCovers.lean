import ThreeUniformDiaries.DiaryPersistentFiniteCoverCertificate
import ThreeUniformDiaries.DiaryUpperBoundCofinalCertifiedFusion

/-!
# Track A: sharp cofinal diary upper from EXPLICIT finite-stage covers

The verified cofinal certified-fusion upper theorem needs only that
each ordinary induced selfcopy w₀ has SOME further induced subcopy i
admitting CertifiedDiaryFusionData on the prescribed leaf range
F∘w₀∘i. This module derives that Type-valued certificate from the
independent finite-horizon criterion exported in the preceding
module: every finitely persistent source leaf stage in that range
admits a genuinely FINITE set of possible next-leaf images covering
every later finite horizon.

Unlike the abstract cofinal Safe certificate, the new hypothesis
is expressed ENTIRELY through the already verified finite
ReservedDiaryStage and CofinalDiaryStageCompatible data, with no
reference to an infinite embedding. The proof uses finite-choice
diagonalisation to obtain persistent successors, then the checked
certified countable fusion theorem.

This is a reduction, NOT a proof that the required finite covers
actually exist for arbitrary prescribed leaf ranges. It does not
assume countable diary unavoidability or the final diary Ramsey
theorem. The exact labelled palette and full TypeRespecting
selfembedding remain the conclusions once the finite covers are
independently established.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- A COFINAL finite-horizon cover condition: for every candidate
ordinary upper selfcopy w₀ there is SOME further unordered induced
selfcopy i such that every persistent finite stage in the refined
prescribed leaf range F[w₀(i[U])] has a FINITE next-image cover.

The condition does not presuppose a countable diary embedding.
It is strictly a predicate about independently checked finite
reserved stages at arbitrary finite horizons. -/
def HasCofinalPersistentFiniteNextLeafCovers
    {U H : Ordered3Graph Nat}
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H) : Prop :=
  ∀ w₀ : UnorderedEmbedding U U,
    ∃ i : UnorderedEmbedding U U,
      ∀ m : Nat, IsLeaf H m →
        ∀ f : Nat → Nat,
          PersistentReservedDiaryStage H H
            (fun t => F (w₀ (i t))) m f →
          FiniteHorizonNextLeafCover H H
            (fun t => F (w₀ (i t))) m f

/-- Cofinal persistent FINITE covers supply exactly the
NONEMPTY certified Safe-stage system required by the
previously verified sharp Track A diary-upper bridge.

The existence of the finite covers remains an independent
and explicit Track D obligation. -/
theorem hasCofinalCertifiedDiaryFusion_of_persistent_finite_covers
    {U H : Ordered3Graph Nat}
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H)
    (hLeaf : ∀ t : Nat, IsLeaf H (F t))
    (hUniversal : CountablyUniversal U)
    (hCovers : HasCofinalPersistentFiniteNextLeafCovers D F) :
    HasCofinalCertifiedDiaryFusion D F := by
  classical
  intro w₀
  obtain ⟨i, hFinite⟩ := hCovers w₀
  let Fi : UnorderedEmbedding U H := F.comp (w₀.comp i)
  have hFiLeaf : ∀ t : Nat, IsLeaf H (Fi t) := by
    intro t
    exact hLeaf (w₀ (i t))
  refine ⟨i, ?_⟩
  change Nonempty (CertifiedDiaryFusionData D H
    (fun t => Fi t))
  exact nonempty_certifiedFusion_of_persistent_finite_covers
    D D hUniversal Fi hFiLeaf hFinite

/-- The sharp FULL diary upper bound on ALL genuine labelled
leaf A-copies, with a complete marker-fixed TypeRespecting
induced diary selfembedding, under the independent cofinal
FINITE next-image cover condition.

This theorem has no external generic G parameter, does not
require F to be increasing or surjective onto all diary leaves,
and counts all increasing presentations of unordered A with
exactly ONE automorphism multiplier. -/
theorem actualFiniteAuxRamsey_allDiaryLeaf_upper_of_cofinal_finite_covers
    (U H : Ordered3Graph Nat)
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H)
    (hLeaf : ∀ t : Nat, IsLeaf H (F t))
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : {v : Fin a → Nat // IsDiaryLeafLabelledCopy A H v} → κ)
    (hCovers : HasCofinalPersistentFiniteNextLeafCovers D F) :
    ∃ (h : Ordered3Graph.Embedding H H)
      (palette : List κ),
        palette.length =
          (∑ P ∈ allIncreasingPresentations A,
            (unmarkedDiariesOfIncreasingPresentation A P).card) *
          Fintype.card
            (FiniteHypergraphAut A.toOrdered3Graph a) ∧
        h.TypeRespecting ∧
        (h 0 = 0 ∧ h 1 = 1 ∧ h 2 = 2) ∧
        ∀ v : Fin a → Nat,
          IsDiaryLeafLabelledCopy A H v →
          ∃ hOutput :
              IsDiaryLeafLabelledCopy A H (fun j => h (v j)),
            χ ⟨(fun j => h (v j)), hOutput⟩ ∈ palette := by
  exact actualFiniteAuxRamsey_allDiaryLeaf_upper_of_cofinalCertifiedFusion
    U H D F hLeaf hUniversal A χ
    (hasCofinalCertifiedDiaryFusion_of_persistent_finite_covers
      D F hLeaf hUniversal hCovers)

end ATRFiniteDecoder
end ThreeUniformDiaries
