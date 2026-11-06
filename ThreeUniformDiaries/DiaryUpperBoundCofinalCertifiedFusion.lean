import ThreeUniformDiaries.DiaryUpperBoundUnorderedLeafCopyNoGeneric

/-!
# Track A: sharp diary upper bound from COFINAL certified Safe subcopies

The previous verified conditional diary upper theorem asks for an
actual CertifiedDiaryFusionData for EVERY ordinary induced U-selfcopy w.
That can be unnecessarily strong. The finite auxiliary Ramsey theorem
only produces one stabilising upper copy w₀ for the given colouring.

It suffices to require that every such w₀ has SOME FURTHER unordered
induced selfcopy i:U→U such that the prescribed leaf range
  F[w₀[i[U]]]
has a certified Safe-stage finite fusion system. Any palette stabilised
by w₀ remains stabilised after composing with i, since an induced
A-copy mapped through i is still an actual induced A-copy of U.

Thus the weaker cofinal certificate condition below yields the SAME
sharp palette on ALL genuine diary leaf A-copies and a marker-fixed
fully TypeRespecting induced diary self-embedding, with no external
generic model, no numerical order condition on F, and no leaf
surjectivity. The certificate still has to be constructed
independently from finite data by Track D. This is a reduction,
NOT an unconditional diary Ramsey or countable unavoidability proof.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- Every candidate upper selfcopy has SOME further induced
selfcopy whose prescribed diary leaf range admits a certified
finite Safe-stage fusion. This is weaker than asking for a
certificate on EVERY originally chosen upper selfcopy. -/
def HasCofinalCertifiedDiaryFusion
    {U H : Ordered3Graph Nat}
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H) : Prop :=
  ∀ w₀ : UnorderedEmbedding U U,
    ∃ i : UnorderedEmbedding U U,
      Nonempty (CertifiedDiaryFusionData D H
        (fun t => F (w₀ (i t))))

/-- The previously used uniform 'for every w' certificate
condition implies the cofinal condition, by choosing
the identity further selfembedding. The reverse implication
is neither assumed nor required. -/
theorem hasCofinalCertifiedDiaryFusion_of_all
    {U H : Ordered3Graph Nat}
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H)
    (hAll : ∀ w : UnorderedEmbedding U U,
      CertifiedDiaryFusionData D H (fun t => F (w t))) :
    HasCofinalCertifiedDiaryFusion D F := by
  intro w₀
  let identity : UnorderedEmbedding U U := {
    toFun := id
    injective := by
      intro a b h
      exact h
    edge_iff := by
      intro a b c _ _
      rfl
  }
  refine ⟨identity, ?_⟩
  change Nonempty (CertifiedDiaryFusionData D H (fun t => F (w₀ t)))
  exact ⟨hAll w₀⟩

/-- Sharp labelled diary upper palette with a fully
TypeRespecting diary selfembedding under only COFINAL
availability of certified finite Safe-stage fusion.

Unlike the previous API there is NO requirement that
every preselected stabilising copy itself admit a certificate:
an extra ordinary induced refinement i may be chosen
after seeing w₀. Its palette inheritance is proved using
actual induced labelled A-embeddings, not arbitrary tuples. -/
theorem actualFiniteAuxRamsey_allDiaryLeaf_upper_of_cofinalCertifiedFusion
    (U H : Ordered3Graph Nat)
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H)
    (hLeaf : ∀ t : Nat, IsLeaf H (F t))
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : {v : Fin a → Nat // IsDiaryLeafLabelledCopy A H v} → κ)
    (hCofinal : HasCofinalCertifiedDiaryFusion D F) :
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
  classical
  let χU :
      {v : Fin a → Nat // IsInducedLabelledCopy A U v} → κ :=
    fun v => χ ⟨(fun j => F (v.1 j)),
      ⟨isInducedLabelledCopy_map_unordered A F v.1 v.2,
        fun j => hLeaf (v.1 j)⟩⟩
  obtain ⟨w₀, palette, hLength, hBound⟩ :=
    actualFiniteAuxRamsey_sharp_upper_on_embeddings_noGeneric
      U hUniversal A χU
  obtain ⟨i, hC⟩ := hCofinal w₀
  let C : CertifiedDiaryFusionData D H
      (fun t => F (w₀ (i t))) := Classical.choice hC
  let w : UnorderedEmbedding U U := w₀.comp i
  have hCertificate :
      CertifiedDiaryFusionData D H (fun t => F (w t)) := by
    change CertifiedDiaryFusionData D H (fun t => F (w₀ (i t)))
    exact C
  obtain ⟨h, hType, hMarkers, hRange⟩ :=
    exists_typeRespecting_fullDiaryEmbedding_of_certified_fusion
      D D (fun t => F (w t)) hCertificate
  refine ⟨h, palette, hLength, hType, hMarkers, ?_⟩
  intro v hv
  let q : Fin a → Nat := fun j =>
    Classical.choose (hRange (v j) (hv.2 j))
  have hImage (j : Fin a) :
      h (v j) = F (w (q j)) :=
    Classical.choose_spec (hRange (v j) (hv.2 j))
  have hCopyImage : IsInducedLabelledCopy A H
      (fun j => h (v j)) :=
    isInducedLabelledCopy_map_unordered A h.asUnordered v hv.1
  have hEq : (fun j : Fin a => h (v j)) =
      (fun j : Fin a => F (w (q j))) := by
    funext j
    exact hImage j
  have hCopyInRange : IsInducedLabelledCopy A H
      (fun j => F (w (q j))) := by
    rw [← hEq]
    exact hCopyImage
  let FW : UnorderedEmbedding U H := F.comp w
  have hQ : IsInducedLabelledCopy A U q :=
    isInducedLabelledCopy_pullback_unordered A FW q hCopyInRange
  have hRefinedCopy : IsInducedLabelledCopy A U
      (fun j => i (q j)) :=
    isInducedLabelledCopy_map_unordered A i q hQ
  have hLeafImage :
      ∀ j : Fin a, IsLeaf H (h (v j)) := by
    intro j
    rw [hImage j]
    exact hLeaf (w (q j))
  have hOutput : IsDiaryLeafLabelledCopy A H
      (fun j => h (v j)) := ⟨hCopyImage, hLeafImage⟩
  let target :
      {s : Fin a → Nat // IsDiaryLeafLabelledCopy A H s} :=
    ⟨(fun j => F (w (q j))),
      ⟨isInducedLabelledCopy_map_unordered A F
        (fun j => w (q j))
        (isInducedLabelledCopy_map_unordered A w q hQ),
       fun j => hLeaf (w (q j))⟩⟩
  have hTargetColour : χ target ∈ palette := by
    have hb := hBound (fun j => i (q j)) hRefinedCopy
    change χ target ∈ palette at hb
    exact hb
  have hSubtypeEq :
      (⟨(fun j => h (v j)), hOutput⟩ :
        {s : Fin a → Nat // IsDiaryLeafLabelledCopy A H s}) =
      target := by
    apply Subtype.ext
    exact hEq
  refine ⟨hOutput, ?_⟩
  rw [hSubtypeEq]
  exact hTargetColour

end ATRFiniteDecoder
end ThreeUniformDiaries
