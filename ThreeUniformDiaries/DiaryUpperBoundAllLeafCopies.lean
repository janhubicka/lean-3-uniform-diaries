import ThreeUniformDiaries.DiaryUpperBoundFullDiaryTypeRespectingLift

/-!
# Track A: sharp upper palette on ALL genuine diary leaf copies

The completed conditional full type-respecting diary self-embedding
theorem controls labelled finite A-copies presented through a chosen
universal hypergraph embedding F : U → H. The printed diary theorem
needs control of EVERY labelled A-copy in the genuine leaf reduct of H.

Track B's verified exact leaf-reduct construction supplies precisely
the additional property needed: F has image all true H-leaves.
Using that surjectivity, pull back every diary leaf copy to an actual
A-copy of U, apply the candidate-conditioned type-respecting diary
upper result, and transport the stabilised colours back to leaf copies
of H. No identification of an arbitrary proper leaf subcopy with
the entire leaf reduct is made.

The still-unproved input is exactly the uniform finite reserved-stage
candidate-realisation condition from Track D. The result is not an
unconditional countable unavoidability or diary Ramsey theorem.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- A genuine labelled A-copy of the leaf reduct of a countable diary.
Unlike a tuple whose image merely lies in a selected universal subcopy,
all entries are explicitly genuine leaves. -/
def IsDiaryLeafLabelledCopy
    {a : Nat} (A : EnumNode a)
    (H : Ordered3Graph Nat) (v : Fin a → Nat) : Prop :=
  IsInducedLabelledCopy A H v ∧ ∀ i : Fin a, IsLeaf H (v i)

/-- Given an exact leaf-reduct presentation F:U→H and the explicit
finite reserved-stage candidate-existence condition, the sharp
labelled palette is realised by an actual type-respecting diary
self-embedding on ALL genuine labelled leaf A-copies of H.

The conclusion is intentionally conditional on candidate-realisation,
not on any claimed proof of countable diary unavoidability. -/
theorem actualFiniteAuxRamsey_allDiaryLeaf_upper_of_reserved_candidates
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
    (hCandidate : ∀ w : UnorderedEmbedding U U,
      ∀ m : Nat, IsLeaf H m →
        ∀ f : Nat → Nat,
          ReservedDiaryStage H H (fun t => F (w t)) m f →
          ∃ v : Nat,
            FiniteNewLeafCandidateCondition H H
              (fun t => F (w t)) m f v ∧
            FutureOrderReserve H (m + 1)
              (candidateNewLeafTableMap H H m f v)) :
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
  obtain ⟨w, h, palette, hLength, hType, hMarkers,
      hRange, hColour⟩ :=
    actualFiniteAuxRamsey_fullDiary_upper_of_reserved_candidates
      G U H D F hLeaf hUniversal A χU hCandidate
  refine ⟨h, palette, hLength, hType, hMarkers, ?_⟩
  intro v hv
  let q : Fin a → Nat := fun i =>
    Classical.choose (hLeafSurj (v i) (hv.2 i))
  have hFq (i : Fin a) : F (q i) = v i :=
    Classical.choose_spec (hLeafSurj (v i) (hv.2 i))
  have hQMap : IsInducedLabelledCopy A H
      (fun i => F (q i)) := by
    have heq : (fun i : Fin a => F (q i)) = v := by
      funext i
      exact hFq i
    rw [heq]
    exact hv.1
  have hQ : IsInducedLabelledCopy A U q :=
    isInducedLabelledCopy_pullback_unordered
      A F.asUnordered q hQMap
  obtain ⟨r, hr, hImage, hInPalette⟩ := hColour q hQ
  have hTuple : (fun i : Fin a => h (v i)) =
      (fun i : Fin a => F (w (r i))) := by
    funext i
    calc
      h (v i) = h (F (q i)) := congrArg h (hFq i).symm
      _ = F (w (r i)) := hImage i
  have hCopyH : IsInducedLabelledCopy A H
      (fun i => h (v i)) :=
    isInducedLabelledCopy_map_unordered A h.asUnordered v hv.1
  have hLeavesH :
      ∀ i : Fin a, IsLeaf H (h (v i)) := by
    intro i
    obtain ⟨t, ht⟩ := hRange (v i) (hv.2 i)
    rw [ht]
    exact hLeaf (w t)
  have hOut : IsDiaryLeafLabelledCopy A H
      (fun i => h (v i)) := ⟨hCopyH, hLeavesH⟩
  let target :
      {s : Fin a → Nat // IsDiaryLeafLabelledCopy A H s} :=
    ⟨(fun i => F (w (r i))),
      ⟨isInducedLabelledCopy_map_unordered A F.asUnordered
        (fun i => w (r i))
        (isInducedLabelledCopy_map_unordered A w r hr),
       fun i => hLeaf (w (r i))⟩⟩
  have hTargetColour : χ target ∈ palette := by
    change χ target ∈ palette at hInPalette
    exact hInPalette
  have hSubtypeEq :
      (⟨(fun i => h (v i)), hOut⟩ :
        {s : Fin a → Nat // IsDiaryLeafLabelledCopy A H s}) =
      target := by
    apply Subtype.ext
    exact hTuple
  refine ⟨hOut, ?_⟩
  rw [hSubtypeEq]
  exact hTargetColour

end ATRFiniteDecoder
end ThreeUniformDiaries
