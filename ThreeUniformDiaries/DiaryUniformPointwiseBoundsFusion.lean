import ThreeUniformDiaries.DiaryFiniteBoundedStageFronts
import ThreeUniformDiaries.DiaryFiniteFrontCertifiedFusion

/-!
# Track B: uniform pointwise stage bounds imply countable diary fusion

The finite-front compactness theorem is now kernel verified:
nonempty FINITE families of genuine admissible cofinal diary
support maps, closed under restriction, yield a certified countable
fusion and hence a full induced diary embedding.

The bounded stage-code module provides canonical total maps which
vanish outside the finite support S_m, with values inside Fin B.

Here we connect them. Suppose there is one function cap : Nat -> Nat
such that at EVERY finite stage m some genuinely admissible map f_m
satisfies f_m(u) < cap(u) for all u in the actual support S_m.
No coherence is assumed among those independently chosen maps.

The collection of all admissible canonical support maps satisfying
these pointwise bounds is a FINITE, NONEMPTY, restriction-closed
front system. Restriction closure is automatic because the bound
cap(u) depends only on u, not on the stage. Finite-front compactness
then constructs one countable full diary embedding preserving edges,
nonedges, roles, and all nonmarker numerical meets.

This is conditional on the STAGE-INDEPENDENT pointwise bound function.
The finite strong flip absorber and genericity do NOT establish
such bounds. No countable-source flip property is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- All stage-m maps with values bounded by a single source-vertex
profile cap. The ambient code space is finite because S_m is
finite and its maximum cap is a natural number. -/
noncomputable def pointwiseBoundedDiaryStageFront
    (H K : Ordered3Graph Nat) (F cap : Nat → Nat) (m : Nat) :
    Finset (Nat → Nat) := by
  classical
  let S := countableDiaryFiniteSupport H m
  exact (boundedSupportCodes S (S.sup cap)).filter
    (fun f => AdmissibleCofinalDiaryStage H K F m f ∧
      ∀ u : Nat, u ∈ S → f u < cap u)

/-- A membership interface to avoid hiding either the real
admissibility or the source-vertex bound condition. -/
theorem mem_pointwiseBoundedDiaryStageFront_iff
    (H K : Ordered3Graph Nat) (F cap : Nat → Nat)
    (m : Nat) (f : Nat → Nat) :
    f ∈ pointwiseBoundedDiaryStageFront H K F cap m ↔
      f ∈ boundedSupportCodes
          (countableDiaryFiniteSupport H m)
          ((countableDiaryFiniteSupport H m).sup cap) ∧
        AdmissibleCofinalDiaryStage H K F m f ∧
        (∀ u : Nat, u ∈ countableDiaryFiniteSupport H m →
          f u < cap u) := by
  classical
  simp [pointwiseBoundedDiaryStageFront]

/-- Any admissible finite stage obeying the global pointwise bound
has an ACTUAL bounded canonical representative in the finite front.
All meet vertices are preserved by the previously verified
normalize_on_support theorem. -/
theorem pointwiseBoundedDiaryStageFront_mem_normalized
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (F cap : Nat → Nat)
    (m : Nat) (f : Nat → Nat)
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hPoint : ∀ u : Nat,
      u ∈ countableDiaryFiniteSupport H m → f u < cap u) :
    canonicalSupportMap (countableDiaryFiniteSupport H m) f ∈
      pointwiseBoundedDiaryStageFront H K F cap m := by
  classical
  let S := countableDiaryFiniteSupport H m
  have hBound : ∀ u : Nat, u ∈ S → f u < S.sup cap := by
    intro u hu
    exact lt_of_lt_of_le (hPoint u hu) (Finset.le_sup hu)
  apply (mem_pointwiseBoundedDiaryStageFront_iff H K F cap m
    (canonicalSupportMap S f)).mpr
  refine ⟨canonicalSupportMap_mem_boundedSupportCodes
      S (S.sup cap) f hBound, ?_, ?_⟩
  · exact AdmissibleCofinalDiaryStage.normalize_on_support
      DH F m f P
  · intro u hu
    rw [canonicalSupportMap_eq_on S f u hu]
    exact hPoint u hu

/-- A uniform per-source-vertex image bound and INDEPENDENT
bounded finite-stage existence construct a genuine finite-front
system. The backwards property needs no chosen compatible family:
an arbitrary later canonical code may simply be restricted and
normalised to the smaller support, retaining the SAME pointwise
bounds on every old source vertex. -/
noncomputable def finiteDiaryFronts_of_pointwiseBounds
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (F cap : Nat → Nat)
    (hEvery : ∀ m : Nat,
      ∃ f : Nat → Nat,
        AdmissibleCofinalDiaryStage H K F m f ∧
        (∀ u : Nat, u ∈ countableDiaryFiniteSupport H m →
          f u < cap u)) :
    FiniteCofinalDiaryFronts DH K F where
  front := fun m => pointwiseBoundedDiaryStageFront H K F cap m
  nonempty := by
    intro m
    obtain ⟨f,P,hPoint⟩ := hEvery m
    exact ⟨canonicalSupportMap (countableDiaryFiniteSupport H m) f,
      pointwiseBoundedDiaryStageFront_mem_normalized
        DH F cap m f P hPoint⟩
  admissible := by
    intro m f hf
    exact ((mem_pointwiseBoundedDiaryStageFront_iff
      H K F cap m f).mp hf).2.1
  backward := by
    intro m n hmn g hg
    have hParts := (mem_pointwiseBoundedDiaryStageFront_iff
      H K F cap n g).mp hg
    have Pn : AdmissibleCofinalDiaryStage H K F n g := hParts.2.1
    have hnPoint : ∀ u : Nat,
        u ∈ countableDiaryFiniteSupport H n → g u < cap u :=
      hParts.2.2
    have Pm : AdmissibleCofinalDiaryStage H K F m g :=
      Pn.restrict hmn
    have hmPoint : ∀ u : Nat,
        u ∈ countableDiaryFiniteSupport H m → g u < cap u := by
      intro u hu
      exact hnPoint u (countableDiaryFiniteSupport_mono H m n hmn hu)
    let S := countableDiaryFiniteSupport H m
    refine ⟨canonicalSupportMap S g, ?_, ?_⟩
    · exact pointwiseBoundedDiaryStageFront_mem_normalized
        DH F cap m g Pm hmPoint
    · intro u hu
      exact (canonicalSupportMap_eq_on S g u hu).symm

/-- Uniform source-vertex image caps reduce countable full diary
embedding to independent bounded finite-stage existence. This
is a completely explicit sufficient compactness gate:
  forall m, exists a valid stage with f_m(u) < cap(u).
It is NOT a consequence of arbitrary individual finite embedding
existence where the bound may grow with m. -/
theorem exists_fullDiaryEmbedding_of_pointwiseBounds
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (F cap : Nat → Nat)
    (hEvery : ∀ m : Nat,
      ∃ f : Nat → Nat,
        AdmissibleCofinalDiaryStage H K F m f ∧
        (∀ u : Nat, u ∈ countableDiaryFiniteSupport H m →
          f u < cap u)) :
    ∃ e : Ordered3Graph.Embedding H K,
      (∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t) ∧
      (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
        K.oneMeetLevel (e u) (e v) =
          e (H.oneMeetLevel u v)) ∧
      (∀ a b c d : Nat, a < b → c < d →
        3 ≤ a → 3 ≤ c →
        K.twoMeetLevel (e a) (e b) (e c) (e d) =
          e (H.twoMeetLevel a b c d)) := by
  exact (finiteDiaryFronts_of_pointwiseBounds
    DH F cap hEvery).exists_full_embedding DK

end DiaryLeafPriority
end ThreeUniformDiaries
