import ThreeUniformDiaries.DiarySharpUpperOnEmbeddings
import ThreeUniformDiaries.DiaryFiniteReservedCandidateFusion

/-!
# Track A: a marker-fixed diary upper lift from explicit reserved candidates

The sharp upper Ramsey palette on ACTUAL labelled A-embeddings is
unconditional (Track A). Countable diary unavoidability remains open
(Track D), but its verified finite generator-table and future-order-
reserve machinery provides a precise conditional source of a full
diary embedding.

The existing full-embedding existence endpoint does not export marker
fixation. The coherent-stage proof does: we recover it directly from
its certified pointwise limit, retaining all three marker equations.

We then turn a sharp ambient induced self-copy w : U → U into a
marker-fixed full numeric-meet diary self-embedding h : H → H whose
leaf range lies in e[w[U]], CONDITIONAL ONLY on the concrete finite
candidate-realisation condition for that range. A labelled A-copy
in the image of the diary map is explicitly pulled back along
e ∘ w, so its colour lies in the sharp ambient palette.

No countable diary unavoidability, final diary Ramsey theorem,
or unproved genericity-to-candidate existence implication is used.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- Reflection of genuine labelled induced A-copies along an unordered
induced embedding. Unlike a mere image-inclusion argument, this
checks ALL source increasing labelled triples and reflects nonedges. -/
theorem isInducedLabelledCopy_pullback_unordered
    {a : Nat} (A : EnumNode a)
    {U H : Ordered3Graph Nat}
    (F : UnorderedEmbedding U H)
    (v : Fin a → Nat)
    (hCopy : IsInducedLabelledCopy A H (fun i => F (v i))) :
    IsInducedLabelledCopy A U v := by
  have hInj : Function.Injective v := by
    intro i j hij
    apply hCopy.1
    exact congrArg F hij
  refine ⟨hInj, ?_⟩
  intro i j k hij hjk
  have hvi : v i ≠ v j := by
    intro he
    exact (ne_of_lt hij) (hInj he)
  have hvik : v i ≠ v k := by
    intro he
    exact (ne_of_lt (lt_trans hij hjk)) (hInj he)
  have hvjk : v j ≠ v k := by
    intro he
    exact (ne_of_lt hjk) (hInj he)
  exact (hCopy.2 i j k hij hjk).trans
    (F.edge_iff_distinct (v i) (v j) (v k)
      hvi hvik hvjk).symm

/-- The coherent finite fusion witness has a marker-fixed induced
limit. This is stronger than the already exported full-embedding
endpoint, which retained numeric meets but did not record 0/1/2. -/
theorem exists_markerFixed_fullDiaryEmbedding_of_reserved_finite_candidates
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (F : Nat → Nat)
    (hCandidate : ∀ m : Nat, IsLeaf H m →
      ∀ f : Nat → Nat,
        ReservedDiaryStage H K F m f →
        ∃ v : Nat,
          FiniteNewLeafCandidateCondition H K F m f v ∧
          FutureOrderReserve H (m + 1)
            (candidateNewLeafTableMap H K m f v)) :
    ∃ e : Ordered3Graph.Embedding H K,
      (e 0 = 0 ∧ e 1 = 1 ∧ e 2 = 2) ∧
      (∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t) ∧
      (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
        K.oneMeetLevel (e u) (e v) =
          e (H.oneMeetLevel u v)) ∧
      (∀ a b c d : Nat, a < b → c < d →
        3 ≤ a → 3 ≤ c →
        K.twoMeetLevel (e a) (e b) (e c) (e d) =
          e (H.twoMeetLevel a b c d)) := by
  classical
  let C : CertifiedDiaryFusionData DH K F := {
    Safe := fun m f => ReservedDiaryStage H K F m f
    valid := by
      intro m f hf
      exact hf.1
    initial := by
      exact ⟨fun u : Nat => u, ReservedDiaryStage.marker_base DH DK F⟩
    next := by
      intro m f hf
      by_cases hm : IsLeaf H m
      · obtain ⟨v, hFinite⟩ := hCandidate m hm f hf
        obtain ⟨g, hStage, hKeep, hNew, hReserve⟩ :=
          (AdmissibleCofinalDiaryStage.reserved_successor_iff_finite_reserved_candidate
            DH hf.1 hm v).mpr hFinite
        have hCompat : CofinalDiaryStageCompatible H m f g :=
          hf.1.successor_compatible_of_selected_leaf_agreement hStage hKeep
        exact ⟨g, ⟨hStage, hReserve⟩, hCompat⟩
      · exact ⟨f, hf.extend_of_not_leaf hm, by intro u hu; rfl⟩
  }
  obtain ⟨P, hStageRange⟩ := C.exists_coherent
  obtain ⟨e, hEq, hOne, hTwo⟩ := P.exists_full_embedding DK
  have hSpec : DiaryPreembeddingSpec H K P.limit :=
    P.limit_is_diaryPreembedding
  have hMarkers : e 0 = 0 ∧ e 1 = 1 ∧ e 2 = 2 := by
    exact ⟨(hEq 0).trans hSpec.marker_zero,
      (hEq 1).trans hSpec.marker_one,
      (hEq 2).trans hSpec.marker_two⟩
  have hRange :
      ∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t := by
    intro u hu
    obtain ⟨t, ht⟩ := P.limit_leaf_range F hStageRange u hu
    exact ⟨t, (hEq u).trans ht⟩
  exact ⟨e, hMarkers, hRange, hOne, hTwo⟩

/-- The sharp upper bound lifts to a marker-fixed genuine numeric-
meet diary self-embedding, provided *each* reserved stage for the
chosen ordinary upper copy has a target leaf satisfying Track D's
explicit finite generator-table and numerical future-reserve tests.

The conclusion records the exact image of every labelled A-copy
after the diary map: it lies in the same ambient upper-copy range
and comes from an actual A-copy, not an arbitrary vertex tuple.

The existence of candidate witnesses is the only OPEN mathematical
hypothesis; this theorem does not discharge it. -/
theorem actualFiniteAuxRamsey_diary_upper_of_reserved_candidates
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
        (h 0 = 0 ∧ h 1 = 1 ∧ h 2 = 2) ∧
        (∀ u : Nat, IsLeaf H u →
          ∃ t : Nat, h u = F (w t)) ∧
        (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
          H.oneMeetLevel (h u) (h v) =
            h (H.oneMeetLevel u v)) ∧
        (∀ x y z t : Nat, x < y → z < t →
          3 ≤ x → 3 ≤ z →
          H.twoMeetLevel (h x) (h y) (h z) (h t) =
            h (H.twoMeetLevel x y z t)) ∧
        ∀ v : Fin a → Nat,
          ∀ hv : IsInducedLabelledCopy A U v,
            ∃ q : Fin a → Nat,
              ∃ hq : IsInducedLabelledCopy A U q,
                (∀ i : Fin a,
                  h (F (v i)) = F (w (q i))) ∧
                χ ⟨(fun i => w (q i)),
                  isInducedLabelledCopy_map_unordered A w q hq⟩ ∈ palette := by
  classical
  obtain ⟨w, palette, hLength, hBound⟩ :=
    actualFiniteAuxRamsey_sharp_upper_on_embeddings
      G U hUniversal A χ
  obtain ⟨h, hMarkers, hRange, hOne, hTwo⟩ :=
    exists_markerFixed_fullDiaryEmbedding_of_reserved_finite_candidates
      D D (fun t => F (w t)) (hCandidate w)
  refine ⟨w, h, palette, hLength, hMarkers, hRange, hOne, hTwo, ?_⟩
  intro v hv
  let q : Fin a → Nat := fun i =>
    Classical.choose (hRange (F (v i)) (hLeaf (v i)))
  have hImage (i : Fin a) :
      h (F (v i)) = F (w (q i)) := by
    exact Classical.choose_spec
      (hRange (F (v i)) (hLeaf (v i)))
  have hOldCopy : IsInducedLabelledCopy A H
      (fun i => h (F (v i))) :=
    isInducedLabelledCopy_map_unordered A h.asUnordered
      (fun i => F (v i))
      (isInducedLabelledCopy_map_unordered A F.asUnordered v hv)
  have hSame : (fun i : Fin a => h (F (v i))) =
      (fun i : Fin a => F (w (q i))) := by
    funext i
    exact hImage i
  have hNewCopy : IsInducedLabelledCopy A H
      (fun i => F (w (q i))) := by
    rw [← hSame]
    exact hOldCopy
  let FW : UnorderedEmbedding U H :=
    F.asUnordered.comp w
  have hq : IsInducedLabelledCopy A U q :=
    isInducedLabelledCopy_pullback_unordered A FW q hNewCopy
  exact ⟨q, hq, hImage, hBound q hq⟩

end ATRFiniteDecoder
end ThreeUniformDiaries
