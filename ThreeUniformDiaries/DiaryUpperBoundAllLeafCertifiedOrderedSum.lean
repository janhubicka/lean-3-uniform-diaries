import ThreeUniformDiaries.DiaryUpperBoundAllLeafCertifiedFusion
import ThreeUniformDiaries.DiarySumOverAllIncreasingPresentations

/-!
# Track A: exact all-ordered-diary count for the certified all-leaf upper lift

The conditional sharp type-respecting diary upper theorem already
stabilises all genuine labelled A-copies on the entire leaf reduct.
The finite counting theorem from Track C (#1068) proves that the
canonical unmarked source count equals the sum of genuine full diary
counts over EVERY increasing ordered presentation of unordered A.

This file ONLY rewrites the fully established finite count; it
introduces no additional Ramsey argument and no candidate-existence
theorem. The role-sensitive certified Safe-stage fusion premise is
explicit and remains the open countable Track D task.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- Sharp upper palette on every genuine diary-leaf A-copy in the
all-increasing-presentations convention of the manuscript, under
the independent existence of certified finite Safe-stage fusion
data for each ordinary upper copy. -/
theorem actualFiniteAuxRamsey_allDiaryLeaf_upper_orderedDiarySum_of_certified_fusion
    (G : GenericEnumerated3Graph)
    (U H : Ordered3Graph Nat)
    (D : RoleDiary H)
    (F : Ordered3Graph.Embedding U H)
    (hLeaf : ∀ t : Nat, IsLeaf H (F t))
    (hLeafSurj : ∀ u : Nat, IsLeaf H u → ∃ t : Nat, F t = u)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : {v : Fin a → Nat // IsDiaryLeafLabelledCopy A H v} → κ)
    (hCertified : ∀ w : UnorderedEmbedding U U,
      CertifiedDiaryFusionData D H (fun t => F (w t))) :
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
              IsDiaryLeafLabelledCopy A H (fun i => h (v i)),
            χ ⟨(fun i => h (v i)), hOutput⟩ ∈ palette := by
  obtain ⟨h, palette, hlength, hType, hMarkers, hBound⟩ :=
    actualFiniteAuxRamsey_allDiaryLeaf_upper_of_certified_fusion
      G U H D F hLeaf hLeafSurj hUniversal A χ hCertified
  refine ⟨h, palette, ?_, hType, hMarkers, hBound⟩
  rw [unmarkedDiaryCount_eq_sum_allIncreasingPresentations A] at hlength
  exact hlength

end ATRFiniteDecoder
end ThreeUniformDiaries
