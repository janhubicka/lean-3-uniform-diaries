import ThreeUniformDiaries.DiaryUpperBoundAllLeafSafeNoSurj
import ThreeUniformDiaries.DiarySharpUpperNoGenericParameter

/-!
# Track A: sharp certified diary upper from an UNORDERED leaf copy

This improves the merged candidate-conditional upper interface in two
independent ways:

1. The initial universal 3-hypergraph is embedded in the genuine diary
   leaves by an arbitrary UNORDERED induced map F:U→H. There is no
   requirement that F preserve the numerical enumeration or cover all
   target leaves.
2. The explicitly coded enumerated generic from
   DiaryGenericExistenceByPairCode supplies G, and the exact all-ordered
   diary sum from Track C supplies the sharp labelled palette.

The proof pulls back only the OUTPUT of the certified type-respecting
diary self-embedding h. Its finite-stage certificate guarantees that
h maps all genuine leaves into F[w[U]] for a sharp ordinary upper
self-copy w, regardless of the original leaves' placement. Since
F∘w is an unordered INDUCED embedding, reflecting edges and
nonedges produces a genuine labelled A-copy in U. Thus the
stabilised palette controls every image leaf copy in H.

The existence of CertifiedDiaryFusionData for the selected range
F[w[U]] remains the separate OPEN Track D problem. No countable
unavoidability, full diary Ramsey theorem or degree lower-bound
equality is asserted.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- Sharp all-genuine-diary-leaf upper palette from a certified
role-sensitive finite fusion subsystem. NO surjectivity of the
initial universal copy onto the genuine diary leaves is needed.

The proof pulls back each A-copy AFTER applying the diary
self-embedding, using its certified target leaf-range inclusion. -/
theorem actualFiniteAuxRamsey_allDiaryLeaf_upper_unorderedF_noGeneric
    (U H : Ordered3Graph Nat)
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H)
    (hLeaf : ∀ t : Nat, IsLeaf H (F t))
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
  classical
  let χU :
      {v : Fin a → Nat // IsInducedLabelledCopy A U v} → κ :=
    fun v => χ ⟨(fun i => F (v.1 i)),
      ⟨isInducedLabelledCopy_map_unordered
          A F v.1 v.2,
        fun i => hLeaf (v.1 i)⟩⟩
  obtain ⟨w, palette, hLength, hBound⟩ :=
    actualFiniteAuxRamsey_sharp_upper_on_embeddings
      canonicalGenericEnumerated3Graph U hUniversal A χU
  obtain ⟨h, hType, hMarkers, hRange⟩ :=
    exists_typeRespecting_fullDiaryEmbedding_of_certified_fusion
      D D (fun t => F (w t)) (hCertified w)
  rw [unmarkedDiaryCount_eq_sum_allIncreasingPresentations A] at hLength
  refine ⟨h, palette, hLength, hType, hMarkers, ?_⟩
  intro v hv
  let q : Fin a → Nat := fun i =>
    Classical.choose (hRange (v i) (hv.2 i))
  have hImage (i : Fin a) :
      h (v i) = F (w (q i)) :=
    Classical.choose_spec (hRange (v i) (hv.2 i))
  have hCopyImage : IsInducedLabelledCopy A H
      (fun i => h (v i)) :=
    isInducedLabelledCopy_map_unordered
      A h.asUnordered v hv.1
  have hEq : (fun i : Fin a => h (v i)) =
      (fun i : Fin a => F (w (q i))) := by
    funext i
    exact hImage i
  have hCopyInRange : IsInducedLabelledCopy A H
      (fun i => F (w (q i))) := by
    rw [← hEq]
    exact hCopyImage
  let FW : UnorderedEmbedding U H :=
    F.comp w
  have hQ : IsInducedLabelledCopy A U q :=
    isInducedLabelledCopy_pullback_unordered A FW q hCopyInRange
  have hLeafImage :
      ∀ i : Fin a, IsLeaf H (h (v i)) := by
    intro i
    rw [hImage i]
    exact hLeaf (w (q i))
  have hOutput : IsDiaryLeafLabelledCopy A H
      (fun i => h (v i)) :=
    ⟨hCopyImage, hLeafImage⟩
  let target :
      {s : Fin a → Nat // IsDiaryLeafLabelledCopy A H s} :=
    ⟨(fun i => F (w (q i))),
      ⟨isInducedLabelledCopy_map_unordered
        A F (fun i => w (q i))
        (isInducedLabelledCopy_map_unordered A w q hQ),
        fun i => hLeaf (w (q i))⟩⟩
  have hTargetColour : χ target ∈ palette := by
    have hb := hBound q hQ
    change χ target ∈ palette at hb
    exact hb
  have hSubtypeEq :
      (⟨(fun i => h (v i)), hOutput⟩ :
        {s : Fin a → Nat // IsDiaryLeafLabelledCopy A H s}) =
      target := by
    apply Subtype.ext
    exact hEq
  refine ⟨hOutput, ?_⟩
  rw [hSubtypeEq]
  exact hTargetColour


end ATRFiniteDecoder
end ThreeUniformDiaries
