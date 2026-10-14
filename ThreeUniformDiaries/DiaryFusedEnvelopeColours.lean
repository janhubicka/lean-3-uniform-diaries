import ThreeUniformDiaries.DiaryStageColourPersistence

/-!
# Complete finite envelope colours survive countable diary fusion

The stage recursion produces complete singleton/auxiliary-pair/
orientation homogeneity for every small ATR source at every
previously visited cut, and every subsequent stage preserves these
colours. To transfer this information to the countable fusion it
suffices to compare TWO actual finite source images: choose one
stage beyond their distinguished vertex images and the protected
cut, so the fusion and that finite stage agree on all entries
read by the colour.

The complete colour uses only the last two vertices of its native
finite source. Consequently no uniform bound over all source
embeddings, no invented infinite-tail coding and no new Ramsey
theorem are required.

The final theorem decodes equality into agreement of the full
ordered pair 2-type below the correct predecessor target cut
and of its lexicographic orientation. This is the abstract
finite-code version of the manuscript's condition (I3).
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- The chosen fusion of all recursive stabilising stages. -/
noncomputable def orderedDiaryFusion
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F) :
    Embedding G.graph G.graph :=
  Embedding.fusionEmbedding
    (orderedDiaryEmbeddings G K F hF)
    (orderedDiaryEmbeddings_prefixStable G K F hF)

theorem orderedDiaryFusion_aux
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F) :
    (orderedDiaryFusion G K F hF).AuxTypeRespecting :=
  Embedding.fusionEmbedding_auxTypeRespecting
    (orderedDiaryEmbeddings G K F hF)
    (orderedDiaryEmbeddings_prefixStable G K F hF)
    (orderedDiaryEmbeddings_aux G K F hF)

theorem orderedDiaryFusion_eq_stage
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F)
    (k t : Nat) (ht : t < k) :
    orderedDiaryFusion G K F hF t =
      orderedDiaryEmbeddings G K F hF k t :=
  Embedding.fusionEmbedding_eq_stage
    (orderedDiaryEmbeddings G K F hF)
    (orderedDiaryEmbeddings_prefixStable G K F hF)
    k t ht

/-- If the two actual finite source endpoints are already below
stage k, evaluating their full colour after the fusion agrees
exactly with evaluating it after stage k. -/
theorem fullEnvelopeColour_fusion_eq_stage
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Nat → Nat) (N : Nat)
    (g : Nat → Embedding G.graph G.graph)
    (hs : Embedding.PrefixStable g)
    (haux : ∀ k, (g k).AuxTypeRespecting)
    {i : Nat} (A : ProtectedSource i) (e : A.Code G)
    (k : Nat)
    (hpen : e.image A.penultimateIndex < k)
    (hlast : e.image A.lastIndex < k) :
    fullEnvelopeColour K F N A
      (e.postcompose (Embedding.fusionEmbedding g hs)
        (Embedding.fusionEmbedding_auxTypeRespecting g hs haux)) =
    fullEnvelopeColour K F N A
      (e.postcompose (g k) (haux k)) := by
  have hp := Embedding.fusionEmbedding_eq_stage g hs k
    (e.image A.penultimateIndex) hpen
  have hl := Embedding.fusionEmbedding_eq_stage g hs k
    (e.image A.lastIndex) hlast
  simp only [fullEnvelopeColour,
    FiniteAuxEmbeddingImage.postcompose_apply, hp, hl]

/-- All complete source-envelope type/orientation colours agree
on every two prefix-fixing finite embeddings of the SAME native
source after countable fusion. The target cut is the correct
image of the protected predecessor, plus one. -/
theorem orderedDiaryFusion_fullEnvelopeColour_pairwise
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F)
    (i : Nat) (hi : 0 < i)
    (A : ProtectedSource i) (hA : A ∈ smallSourceUniverse i)
    (e₀ e₁ : A.Code G)
    (he₀ : A.FixesPrefix G e₀)
    (he₁ : A.FixesPrefix G e₁) :
    fullEnvelopeColour K F
      (F (orderedDiaryFusion G K F hF (i-1)) + 1) A
      (e₀.postcompose (orderedDiaryFusion G K F hF)
        (orderedDiaryFusion_aux G K F hF)) =
    fullEnvelopeColour K F
      (F (orderedDiaryFusion G K F hF (i-1)) + 1) A
      (e₁.postcompose (orderedDiaryFusion G K F hF)
        (orderedDiaryFusion_aux G K F hF)) := by
  let stages := orderedDiaryEmbeddings G K F hF
  have hs : Embedding.PrefixStable stages :=
    orderedDiaryEmbeddings_prefixStable G K F hF
  have haux : ∀ k, (stages k).AuxTypeRespecting := by
    intro k
    exact orderedDiaryEmbeddings_aux G K F hF k
  let k := i + e₀.image A.penultimateIndex +
    e₀.image A.lastIndex +
    e₁.image A.penultimateIndex + e₁.image A.lastIndex + 1
  have hik : i ≤ k := by dsimp [k]; omega
  have hprev : i - 1 < k := by dsimp [k]; omega
  have hp₀ : e₀.image A.penultimateIndex < k := by
    dsimp [k]; omega
  have hl₀ : e₀.image A.lastIndex < k := by
    dsimp [k]; omega
  have hp₁ : e₁.image A.penultimateIndex < k := by
    dsimp [k]; omega
  have hl₁ : e₁.image A.lastIndex < k := by
    dsimp [k]; omega
  have hCut :
      F (orderedDiaryFusion G K F hF (i-1)) + 1 =
      F (stages k (i-1)) + 1 := by
    exact congrArg (fun x => F x + 1)
      (orderedDiaryFusion_eq_stage G K F hF k (i-1) hprev)
  have hStage :
      fullEnvelopeColour K F (F (stages k (i-1)) + 1) A
        (e₀.postcompose (stages k) (haux k)) =
      fullEnvelopeColour K F (F (stages k (i-1)) + 1) A
        (e₁.postcompose (stages k) (haux k)) := by
    have hStable := orderedDiaryStages_coloursStable G K F hF k
    obtain ⟨color, hcolor⟩ := hStable i hi hik A hA
    exact (hcolor e₀ he₀).trans (hcolor e₁ he₁).symm
  rw [hCut]
  calc
    fullEnvelopeColour K F (F (stages k (i-1)) + 1) A
        (e₀.postcompose (orderedDiaryFusion G K F hF)
          (orderedDiaryFusion_aux G K F hF)) =
      fullEnvelopeColour K F (F (stages k (i-1)) + 1) A
        (e₀.postcompose (stages k) (haux k)) :=
          fullEnvelopeColour_fusion_eq_stage
            G K F (F (stages k (i-1)) + 1) stages hs haux
            A e₀ k hp₀ hl₀
    _ = fullEnvelopeColour K F (F (stages k (i-1)) + 1) A
        (e₁.postcompose (stages k) (haux k)) := hStage
    _ = fullEnvelopeColour K F (F (stages k (i-1)) + 1) A
        (e₁.postcompose (orderedDiaryFusion G K F hF)
          (orderedDiaryFusion_aux G K F hF)) :=
          (fullEnvelopeColour_fusion_eq_stage
            G K F (F (stages k (i-1)) + 1) stages hs haux
            A e₁ k hp₁ hl₁).symm

/-- Decode the common complete colour in the countable fusion:
any two protected finite copies of the SAME small envelope
have equal full ordered-pair 2-type and lexicographic orientation
at the predecessor outer target cut.

For singleton envelopes, the second-coordinate singleton-type
component supplies the one-type conclusion. -/
theorem orderedDiaryFusion_pairType_orientation
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F)
    (i : Nat) (hi : 0 < i)
    (A : ProtectedSource i) (hA : A ∈ smallSourceUniverse i)
    (e₀ e₁ : A.Code G)
    (he₀ : A.FixesPrefix G e₀)
    (he₁ : A.FixesPrefix G e₁) :
    let g := orderedDiaryFusion G K F hF
    let N := F (g (i-1)) + 1
    K.SameTwoTypeBelow N
      (F (g (e₀.image A.penultimateIndex)))
      (F (g (e₀.image A.lastIndex)))
      (F (g (e₁.image A.penultimateIndex)))
      (F (g (e₁.image A.lastIndex))) ∧
    (DiaryLeafPriority.LexEarlier K
        (F (g (e₀.image A.penultimateIndex)))
        (F (g (e₀.image A.lastIndex))) ↔
      DiaryLeafPriority.LexEarlier K
        (F (g (e₁.image A.penultimateIndex)))
        (F (g (e₁.image A.lastIndex)))) := by
  let g := orderedDiaryFusion G K F hF
  let N := F (g (i-1)) + 1
  have hc := orderedDiaryFusion_fullEnvelopeColour_pairwise
    G K F hF i hi A hA e₀ e₁ he₀ he₁
  have hdecoded :=
    (fullEnvelopeColour_eq_iff K F N A
      (e₀.postcompose g (orderedDiaryFusion_aux G K F hF))
      (e₁.postcompose g (orderedDiaryFusion_aux G K F hF))).mp hc
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simpa only [FiniteAuxEmbeddingImage.postcompose_apply]
      using hdecoded.1
  · simpa only [FiniteAuxEmbeddingImage.postcompose_apply]
      using hdecoded.2.1
  · simpa only [FiniteAuxEmbeddingImage.postcompose_apply]
      using hdecoded.2.2.1
  · simpa only [FiniteAuxEmbeddingImage.postcompose_apply]
      using hdecoded.2.2.2

end ATRFiniteDecoder
end ThreeUniformDiaries
