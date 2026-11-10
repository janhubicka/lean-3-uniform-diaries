import ThreeUniformDiaries.DiaryCofinalBoundedCountableFusion
import ThreeUniformDiaries.DiaryUpperBoundMarkerMeetCompletion

/-!
# Critical-path interface audit: the fused embedding retains its diary certificate

The existing countable certified fusion theorem yields an induced ordered
embedding preserving every nonmarker numerical singleton and full pair meet.
Its proof actually constructs a stronger map: a DiaryPreembeddingSpec
fixing all three marker vertices and preserving all genuine diary roles.

Here we export that certificate on the SAME embedding, rather than
claiming it from arbitrary induced embeddings or adding any new
relative-extension hypothesis.

The cofinal bounded-next-image version remains STRICTLY CONDITIONAL
on its original uniform bound for every persistent true-leaf stage.
This module does not prove nonescape, existence of persistent successors,
the countable diary unavoidability theorem, or the diary Ramsey theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The coherent fusion witness is an induced graph embedding AND
a genuine role- and marker-preserving diary preembedding, AND a full
TypeRespecting map by the existing certified marker-completion theorem. All
certificates describe literally the same underlying function. -/
theorem CertifiedDiaryFusionData.exists_full_embedding_with_spec
    {H K : Ordered3Graph Nat} {DH : RoleDiary H}
    {F : Nat → Nat}
    (C : CertifiedDiaryFusionData DH K F)
    (DK : RoleDiary K) :
    ∃ e : Ordered3Graph.Embedding H K,
      DiaryPreembeddingSpec H K (fun u : Nat => e u) ∧
      e.TypeRespecting ∧
      (∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t) ∧
      (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
        K.oneMeetLevel (e u) (e v) =
          e (H.oneMeetLevel u v)) ∧
      (∀ a b c d : Nat, a < b → c < d →
        3 ≤ a → 3 ≤ c →
        K.twoMeetLevel (e a) (e b) (e c) (e d) =
          e (H.twoMeetLevel a b c d)) := by
  obtain ⟨P, hRange⟩ := C.exists_coherent
  obtain ⟨e, heq, hOne, hTwo⟩ := P.exists_full_embedding DK
  have hFun : (fun u : Nat => e u) = P.limit := by
    funext u
    exact heq u
  have hSpec : DiaryPreembeddingSpec H K (fun u : Nat => e u) := by
    rw [hFun]
    exact P.limit_is_diaryPreembedding
  have hTypeRespecting : e.TypeRespecting :=
    e.typeRespecting_of_nonmarker_exact_meets_and_markers
      hSpec.marker_zero hSpec.marker_one hSpec.marker_two hOne hTwo
  refine ⟨e, hSpec, hTypeRespecting, ?_, hOne, hTwo⟩
  intro u hu
  obtain ⟨t, ht⟩ := P.limit_leaf_range F hRange u hu
  exact ⟨t, (heq u).trans ht⟩

/-- If the genuine finite covers are supplied, the full leaf-range
embedding carries an explicit exact diary preembedding certificate.
No additional compactness principle is introduced. -/
theorem exists_fullDiaryEmbedding_of_persistent_finite_covers_with_spec
    {H U K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (hUniversal : Ordered3Graph.CountablyUniversal U)
    (F : Ordered3Graph.UnorderedEmbedding U K)
    (hFleaf : ∀ t : Nat, IsLeaf K (F t))
    (hFiniteCover : ∀ m : Nat, IsLeaf H m →
      ∀ f : Nat → Nat,
        PersistentReservedDiaryStage H K F m f →
        FiniteHorizonNextLeafCover H K F m f) :
    ∃ e : Ordered3Graph.Embedding H K,
      DiaryPreembeddingSpec H K (fun u : Nat => e u) ∧
      e.TypeRespecting ∧
      (∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t) ∧
      (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
        K.oneMeetLevel (e u) (e v) =
          e (H.oneMeetLevel u v)) ∧
      (∀ a b c d : Nat, a < b → c < d →
        3 ≤ a → 3 ≤ c →
        K.twoMeetLevel (e a) (e b) (e c) (e d) =
          e (H.twoMeetLevel a b c d)) := by
  let C : CertifiedDiaryFusionData DH K F := {
    Safe := PersistentReservedDiaryStage H K F
    valid := by
      intro m f P
      exact P.1.1
    initial := by
      exact ⟨fun u => u,
        persistent_reserved_marker_base DH DK G hUniversal F hFleaf⟩
    next := by
      intro m f P
      by_cases hm : IsLeaf H m
      · obtain ⟨g, hPersistent, hCompatible⟩ :=
          exists_persistent_reserved_successor_of_finite_cover
            hm (hFiniteCover m hm f P)
        exact ⟨g, hPersistent, hCompatible⟩
      · exact ⟨f, P.extend_of_not_leaf hm,
          by intro u hu; rfl⟩
  }
  exact C.exists_full_embedding_with_spec DK

/-- The cofinal bounded-image assumption already used for conditional
countable diary fusion yields the STRONG output without additional
existence assumptions. The image bound remains the open critical gate. -/
theorem exists_fullDiaryEmbedding_of_cofinal_bounded_leaf_images_with_spec
    {H U K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (hUniversal : Ordered3Graph.CountablyUniversal U)
    (F : Ordered3Graph.UnorderedEmbedding U K)
    (hFleaf : ∀ t : Nat, IsLeaf K (F t))
    (hBound : ∀ m : Nat, IsLeaf H m →
      ∀ f : Nat → Nat,
        PersistentReservedDiaryStage H K F m f →
        HasCofinalBoundedNextLeafImages H K F f m) :
    ∃ e : Ordered3Graph.Embedding H K,
      DiaryPreembeddingSpec H K (fun u : Nat => e u) ∧
      e.TypeRespecting ∧
      (∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t) ∧
      (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
        K.oneMeetLevel (e u) (e v) =
          e (H.oneMeetLevel u v)) ∧
      (∀ a b c d : Nat, a < b → c < d →
        3 ≤ a → 3 ≤ c →
        K.twoMeetLevel (e a) (e b) (e c) (e d) =
          e (H.twoMeetLevel a b c d)) := by
  exact exists_fullDiaryEmbedding_of_persistent_finite_covers_with_spec
    DH DK canonicalGenericEnumerated3Graph hUniversal F hFleaf
    (by
      intro m hm f P
      exact finiteHorizonNextLeafCover_of_cofinal_bounded_images
        H K F f m (hBound m hm f P))

end DiaryLeafPriority
end ThreeUniformDiaries
