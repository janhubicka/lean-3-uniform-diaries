import ThreeUniformDiaries.DiaryUpperBoundJointSelectedCertifiedCopy

/-!
# Track A: noncircular diary sharp upper as a DIRECT consequence of unavoidability

English-first independent referee proof:
  3-uniform-diaries PR #338.

The FULL diary selfembedding upper is conditional here on the exact
self-case of countable diary unavoidability for each prescribed
unordered induced universal leaf range. This is an OPEN theorem;
we do NOT infer it from the independently verified ordinary sharp
upper, finite diary unavoidability or unrestricted Safe certificates.

The ordinary sharp labelled upper palette is already unconditional.
Select its unordered U selfcopy w, then apply the supplied relative
unavoidability to the EXACT range F∘w. Pull back every labelled H-leaf
A-copy AFTER its diary image under h. Edges and NONEDGES reflect
through the unordered induced embedding F∘w. No use of the FINAL
diary Ramsey theorem, no false type-to-aux transfer, and no assumed
order monotonicity or leaf surjectivity of F.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- A correct conditional replacement for the circular printed
diary-selfembedding upper: ordinary sharp Ramsey plus one application
of independently supplied full countable diary unavoidability.

The unavoidability hypothesis explicitly gives a marker-fixed
TypeRespecting diary selfembedding for EACH prescribed unordered
universal selfcopy w, with all its genuine leaves in F[w[U]].
Its existence is NOT established by this theorem. -/
theorem actualFiniteAuxRamsey_allDiaryLeaf_upper_of_self_unavoidability
    (U H : Ordered3Graph Nat)
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H)
    (hLeaf : ∀ t : Nat, IsLeaf H (F t))
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : {v : Fin a → Nat // IsDiaryLeafLabelledCopy A H v} → κ)
    (hUnavoidable : ∀ w : UnorderedEmbedding U U,
      ∃ h : Ordered3Graph.Embedding H H,
        h.TypeRespecting ∧
        (h 0 = 0 ∧ h 1 = 1 ∧ h 2 = 2) ∧
        (∀ u : Nat, IsLeaf H u →
          ∃ t : Nat, h u = F (w t))) :
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
    actualFiniteAuxRamsey_sharp_upper_on_embeddings_noGeneric
      U hUniversal A χU
  obtain ⟨h, hType, hMarkers, hRange⟩ :=
    hUnavoidable w
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
  let FW : UnorderedEmbedding U H := F.comp w
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
      ⟨isInducedLabelledCopy_map_unordered A F
        (fun i => w (q i))
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
