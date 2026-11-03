import ThreeUniformDiaries.DiaryUpperBoundMarkerMeetCompletion

/-!
# Track A: exact type-respecting diary self-embedding upper lift

The strict fully induced and marker-fixed countable embedding constructed
under Track D's explicit finite reserved-candidate realization hypothesis
is already verified in the previous module. The independent marker
completion lemmas show that preservation of the nonmarker numerical
singleton and full pair meets implies preservation of ALL numerical
meets, including marker-containing comparisons. Consequently that
embedding satisfies the original complete TypeRespecting predicate.

This wrapper matches the exact DIARY-SELF-EMBEDDING output type needed
by the manuscript's upper argument, CONDITIONAL on the still-unproved
finite candidate existence for every reserved stage. It does NOT assert
countable unavoidability or the final diary Ramsey theorem. The
printed upper theorem's malformed colour domain and Aut(A) convention
still require editorial repair; here we use genuine induced labelled
Emb(A,U) colourings and the single sharp |Aut(A)| factor.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- Subject to the independently stated finite reserved-stage candidate
realisation condition, the sharp labelled upper palette lifts to a
marker-fixing, genuinely TypeRespecting, induced diary self-embedding.

In particular, this is stronger than mere preservation of numerical
meets between nonmarker points: ALL singleton and ordered-pair type
comparisons at arbitrary cuts are preserved and reflected. The
candidate-existence hypothesis remains open and visible. -/
theorem actualFiniteAuxRamsey_fullDiary_upper_of_reserved_candidates
    (G : GenericEnumerated3Graph)
    (U H : Ordered3Graph Nat)
    (D : RoleDiary H)
    (F : Ordered3Graph.Embedding U H)
    (hLeaf : ∀ t : Nat, IsLeaf H (F t))
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : {v : Fin a → Nat // IsInducedLabelledCopy A U v} → κ)
    (hCandidate : ∀ w : UnorderedEmbedding U U,
      ∀ m : Nat, IsLeaf H m →
        ∀ f : Nat → Nat,
          ReservedDiaryStage H H (fun t => F (w t)) m f →
          ∃ v : Nat,
            FiniteNewLeafCandidateCondition H H
              (fun t => F (w t)) m f v ∧
            FutureOrderReserve H (m + 1)
              (candidateNewLeafTableMap H H m f v)) :
    ∃ (w : UnorderedEmbedding U U)
      (h : Ordered3Graph.Embedding H H)
      (palette : List κ),
        palette.length =
          (allGenuineUnmarkedDiarySources A).card *
          Fintype.card
            (FiniteHypergraphAut A.toOrdered3Graph a) ∧
        h.TypeRespecting ∧
        (h 0 = 0 ∧ h 1 = 1 ∧ h 2 = 2) ∧
        (∀ u : Nat, IsLeaf H u →
          ∃ t : Nat, h u = F (w t)) ∧
        ∀ v : Fin a → Nat,
          ∀ hv : IsInducedLabelledCopy A U v,
            ∃ q : Fin a → Nat,
              ∃ hq : IsInducedLabelledCopy A U q,
                (∀ i : Fin a,
                  h (F (v i)) = F (w (q i))) ∧
                χ ⟨(fun i => w (q i)),
                  isInducedLabelledCopy_map_unordered A w q hq⟩ ∈ palette := by
  obtain ⟨w, h, palette, hLength, hMarkers, hRange,
      hOne, hTwo, hColour⟩ :=
    actualFiniteAuxRamsey_diary_upper_of_reserved_candidates
      G U H D F hLeaf hUniversal A χ hCandidate
  have hType : h.TypeRespecting :=
    h.typeRespecting_of_nonmarker_exact_meets_and_markers
      hMarkers.1 hMarkers.2.1 hMarkers.2.2
      hOne hTwo
  exact ⟨w, h, palette, hLength, hType, hMarkers,
    hRange, hColour⟩

end ATRFiniteDecoder
end ThreeUniformDiaries
