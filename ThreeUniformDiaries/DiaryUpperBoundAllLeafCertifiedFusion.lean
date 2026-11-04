import ThreeUniformDiaries.DiaryUpperBoundAllLeafCopies
import ThreeUniformDiaries.DiaryUpperBoundCertifiedFusionLift

/-!
# Track A: sharp full-leaf diary upper bound from a certified Safe subsystem

This closes the composition between two independently verified interfaces:
* the exact all-genuine-leaf-copy transfer proved in #1080, and
* the flexible certified finite-stage upper lift proved in #1088.

The ambient hypergraph U is an induced increasing leaf model of a
genuine full diary H, and its image contains ALL genuine H leaves.
Thus any labelled A-copy of H's leaf reduct comes from a genuine
A-copy of U. A separately supplied certified Safe-stage system for
each chosen ordinary upper self-copy produces a marker-fixed,
TypeRespecting H→H self-embedding with sharp labelled palette
card(allGenuineUnmarkedDiarySources A) * |Aut(A)|.

No theorem here constructs the Safe predicate, its initial stage,
or its coherent successor rule. The countable realization question
is still OPEN in Track D. In particular, no countable unavoidability,
diary Ramsey theorem, or sharp degree lower-bound equality follows.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- Given an exact leaf-reduct presentation F:U→H and an independently
constructed, role-sensitive certified finite-stage fusion system, the sharp
labelled palette is realised by an actual type-respecting diary
self-embedding on ALL genuine labelled leaf A-copies of H.

The conclusion is intentionally conditional on certified safe-stage existence,
not on any claimed proof of countable diary unavoidability. -/
theorem actualFiniteAuxRamsey_allDiaryLeaf_upper_of_certified_fusion
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
    actualFiniteAuxRamsey_fullDiary_upper_of_certified_fusion
      G U H D F hLeaf hUniversal A χU hCertified
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
