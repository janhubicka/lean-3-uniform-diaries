import ThreeUniformDiaries.DiaryExactUnlabelledBigRamseyDegree

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open _root_.ThreeUniformDiaries.Ordered3Graph

/-- Every finite A embeds in a countably universal U, hence
the labelled copy domain is nonempty, including when a=0. -/
theorem nonempty_genuineFiniteEmbeddings_of_universal
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a) :
    Nonempty (GenuineFiniteEmbeddings A U) := by
  classical
  let F : UnorderedEmbedding A.toOrdered3Graph U :=
    Classical.choice (hUniversal A.toOrdered3Graph)
  let v : Fin a → Nat := fun i => F i.val
  have hv : IsInducedLabelledCopy A U v := by
    refine ⟨?_, ?_⟩
    · intro i j hij
      apply Fin.ext
      exact F.injective hij
    · intro i j k hij hjk
      exact ((A.toOrdered3Graph.unorderedEdge_iff_of_lt
        i.val j.val k.val hij hjk).symm).trans
        (F.edge_iff i.val j.val k.val hij hjk)
  exact ⟨⟨v, hv⟩⟩

/-- The zero-colour case from the manuscript's quantification
over every finite r is vacuous: an actual A-embedding exists. -/
theorem no_zero_colouring_of_genuine_embeddings
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a) :
    ¬ Nonempty (GenuineFiniteEmbeddings A U → Empty) := by
  rintro ⟨χ⟩
  obtain ⟨v⟩ := nonempty_genuineFiniteEmbeddings_of_universal
    U hUniversal A
  exact (χ v).elim

/-- A standard unlabelled big Ramsey bound, with colourings
defined ONLY on actual induced finite A-copies rather than on
every arbitrary finite vertex set. -/
def IsUnlabelledBigRamseyBoundOnCopies
    (U : Ordered3Graph Nat) {a : Nat} (A : EnumNode a)
    (t : Nat) : Prop :=
  ∀ (κ : Type) [Fintype κ] [Nonempty κ]
      (χ : GenuineUnlabelledCopies A U → κ),
    ∃ (w : UnorderedEmbedding U U) (palette : Finset κ),
      palette.card ≤ t ∧
      ∀ v : GenuineFiniteEmbeddings A U,
        χ ⟨(Finset.univ : Finset (Fin a)).image
            (v.postcompose w).val,
          ⟨v.postcompose w, rfl⟩⟩ ∈ palette

/-- Colouring ALL finite vertex sets, as in the currently
certified exact unlabelled theorem, is EQUIVALENT to colouring
only real induced A-copies. The extension by a default colour
uses no additional assumptions beyond the finite nonempty
colour type already in the Ramsey definition. -/
theorem isUnlabelledBigRamseyBound_iff_onActualCopies
    (U : Ordered3Graph Nat) {a : Nat} (A : EnumNode a)
    (t : Nat) :
    IsUnlabelledBigRamseyBound U A t ↔
      IsUnlabelledBigRamseyBoundOnCopies U A t := by
  classical
  constructor
  · intro hBound κ _ _ χ
    let total : Finset Nat → κ := fun L =>
      if hL : ∃ v : GenuineFiniteEmbeddings A U,
          L = (Finset.univ : Finset (Fin a)).image v.val then
        χ ⟨L, hL⟩
      else Classical.choice (inferInstance : Nonempty κ)
    obtain ⟨w, palette, hCard, hCover⟩ := hBound κ total
    refine ⟨w, palette, hCard, ?_⟩
    intro v
    have hReal :
        ∃ q : GenuineFiniteEmbeddings A U,
          (Finset.univ : Finset (Fin a)).image
              (v.postcompose w).val =
            (Finset.univ : Finset (Fin a)).image q.val :=
      ⟨v.postcompose w, rfl⟩
    have hv := hCover v
    change total ((Finset.univ : Finset (Fin a)).image
      (v.postcompose w).val) ∈ palette at hv
    simpa only [total, dif_pos hReal] using hv
  · intro hBound κ _ _ χ
    let restricted : GenuineUnlabelledCopies A U → κ :=
      fun L => χ L.val
    obtain ⟨w, palette, hCard, hCover⟩ :=
      hBound κ restricted
    refine ⟨w, palette, hCard, ?_⟩
    intro v
    change χ ((Finset.univ : Finset (Fin a)).image
      (v.postcompose w).val) ∈ palette
    simpa only [restricted] using hCover v

end ATRFiniteDecoder
end ThreeUniformDiaries
