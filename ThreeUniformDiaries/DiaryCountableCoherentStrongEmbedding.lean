import ThreeUniformDiaries.DiaryCountableCoherentStageGluing
import ThreeUniformDiaries.DiaryCountableInducedPreembeddingFullMeets

/-!
# Coherent finite diary supports yield a complete countable embedding

Given an ACTUALLY COMPATIBLE family of full finite support maps,
the gluing theorem produces one global diary preembedding which
is induced on ALL source triples. The global E-only marker
dichotomy upgrades this induced map to all numeric singleton
and full ordered-pair meets, including mixed split/leaf cases.

This conclusion is conditional. The existence of a compatible
finite-stage map family is NOT a consequence of independent
finite flip absorbers; that remains the countable-source gate.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {D : RoleDiary H}

/-- No mixed numerical meet information is lost when a compatible
stage-map family has a genuine induced countable limit. -/
theorem CoherentCofinalDiarySupportMaps.limit_all_numeric_meets
    (P : CoherentCofinalDiarySupportMaps D K)
    (DK : RoleDiary K) :
    (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
      K.oneMeetLevel (P.limit u) (P.limit v) =
        P.limit (H.oneMeetLevel u v)) ∧
    (∀ a b c d : Nat, a < b → c < d →
      3 ≤ a → 3 ≤ c →
      K.twoMeetLevel (P.limit a) (P.limit b)
        (P.limit c) (P.limit d) =
          P.limit (H.twoMeetLevel a b c d)) := by
  exact DiaryPreembeddingSpec.all_numerical_meets_of_induced
    D DK P.limit_is_diaryPreembedding
    (by
      intro a b c hab hbc
      exact (P.limit_induced_all_triples a b c hab hbc).symm)

/-- The same pointwise limit is a genuinely induced ordered
embedding with all nonmarker singleton and pair meets exact. -/
theorem CoherentCofinalDiarySupportMaps.exists_full_embedding
    (P : CoherentCofinalDiarySupportMaps D K)
    (DK : RoleDiary K) :
    ∃ e : Ordered3Graph.Embedding H K,
      (∀ u : Nat, e u = P.limit u) ∧
      (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
        K.oneMeetLevel (e u) (e v) = e (H.oneMeetLevel u v)) ∧
      (∀ a b c d : Nat, a < b → c < d →
        3 ≤ a → 3 ≤ c →
        K.twoMeetLevel (e a) (e b) (e c) (e d) =
          e (H.twoMeetLevel a b c d)) := by
  let e : Ordered3Graph.Embedding H K := {
    toFun := P.limit
    strictMono := P.limit_is_diaryPreembedding.strictMono
    edge_iff := by
      intro a b c hab hbc
      exact P.limit_induced_all_triples a b c hab hbc
  }
  obtain ⟨hOne,hTwo⟩ := P.limit_all_numeric_meets DK
  refine ⟨e,?_,?_,?_⟩
  · intro u
    rfl
  · intro u v hu hv
    change K.oneMeetLevel (P.limit u) (P.limit v) =
      P.limit (H.oneMeetLevel u v)
    exact hOne u v hu hv
  · intro a b c d hab hcd ha hc
    change K.twoMeetLevel (P.limit a) (P.limit b)
      (P.limit c) (P.limit d) =
        P.limit (H.twoMeetLevel a b c d)
    exact hTwo a b c d hab hcd ha hc

/-- An explicit prescribed leaf range is retained by the SAME
full induced countable embedding, provided all coherent finite
stages put their true source leaves in that range. -/
theorem CoherentCofinalDiarySupportMaps.exists_full_embedding_in_range
    (P : CoherentCofinalDiarySupportMaps D K)
    (DK : RoleDiary K)
    (F : Nat → Nat)
    (hRange : ∀ m u : Nat,
      u ∈ countableDiaryFiniteSupport H m →
      IsLeaf H u → ∃ t : Nat, P.map m u = F t) :
    ∃ e : Ordered3Graph.Embedding H K,
      (∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t) ∧
      (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
        K.oneMeetLevel (e u) (e v) = e (H.oneMeetLevel u v)) ∧
      (∀ a b c d : Nat, a < b → c < d →
        3 ≤ a → 3 ≤ c →
        K.twoMeetLevel (e a) (e b) (e c) (e d) =
          e (H.twoMeetLevel a b c d)) := by
  obtain ⟨e,hEq,hOne,hTwo⟩ := P.exists_full_embedding DK
  refine ⟨e,?_,hOne,hTwo⟩
  intro u hu
  obtain ⟨t,ht⟩ := P.limit_leaf_range F hRange u hu
  exact ⟨t,(hEq u).trans ht⟩

end DiaryLeafPriority
end ThreeUniformDiaries
