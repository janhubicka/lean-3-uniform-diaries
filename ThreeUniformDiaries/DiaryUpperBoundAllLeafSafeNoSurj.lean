import ThreeUniformDiaries.DiaryUpperBoundAllLeafCertifiedFusion

/-!
# Track A: all-leaf certified diary upper WITHOUT leaf-reduct surjectivity

An adversarial simplification of the all-genuine-leaf sharp upper proof:
we do not need an exact leaf-reduct isomorphism F:U≃leaves(H).
It suffices to have SOME induced universal hypergraph copy F:U→H
landing on genuine H leaves.

Indeed, the certified countable fusion gives a type-respecting
diary self-embedding h:H→H satisfying
  h[leaves(H)] ⊆ F[w[U]]
for the ordinary sharp upper self-copy w:U→U. Given ANY original
A-copy on H's genuine leaves, h maps it to an A-copy inside
F[w[U]]. Pull back the IMAGE, not the original copy, along F∘w.
Inducedness reflects both edges and nonedges, so this preimage
is an actual labelled A-copy of U and the sharp ambient palette
applies. This removes the old hypothesis that every H leaf
lies in F[U].

No countable diary-unavoidability, full diary Ramsey theorem,
or lower bound is proved. The independent certified Safe-stage
extension data remain a visible, unproved Track D hypothesis.
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
theorem actualFiniteAuxRamsey_allDiaryLeaf_upper_of_certified_fusion_noSurj
    (G : GenericEnumerated3Graph)
    (U H : Ordered3Graph Nat)
    (D : RoleDiary H)
    (F : Ordered3Graph.Embedding U H)
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
          (allGenuineUnmarkedDiarySources A).card *
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
          A F.asUnordered v.1 v.2,
        fun i => hLeaf (v.1 i)⟩⟩
  obtain ⟨w, palette, hLength, hBound⟩ :=
    actualFiniteAuxRamsey_sharp_upper_on_embeddings
      G U hUniversal A χU
  obtain ⟨h, hType, hMarkers, hRange⟩ :=
    exists_typeRespecting_fullDiaryEmbedding_of_certified_fusion
      D D (fun t => F (w t)) (hCertified w)
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
    F.asUnordered.comp w
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
        A F.asUnordered (fun i => w (q i))
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
