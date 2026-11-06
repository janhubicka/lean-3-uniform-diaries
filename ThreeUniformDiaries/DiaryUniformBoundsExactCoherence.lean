import ThreeUniformDiaries.DiaryUniformPointwiseBoundsFusion
import ThreeUniformDiaries.DiaryCountableCoherentStageGluing

/-!
# Track B: uniform image caps are EQUIVALENT to coherent finite diary stages

The merged bounded-front criterion gives:
  one fixed vertex-image cap, plus an independently admissible
  bounded finite stage for every finite support
  => a coherent countable family of stages.

The converse is important for adversarial proof audits.
Given any actual coherent family P of admissible stages, the
global limit P.limit exists and restricts to each stage. Choosing
  cap u := P.limit u + 1
bounds the stage images of EVERY u wherever u is in a support.

Thus for a fixed source/target/leaf-range triple the existence
of pointwise uniformly bounded independent admissible stages
is logically EQUIVALENT to the existence of a coherent stage
family. This is a useful exact reformulation, but NOT a
replacement for the missing relative geometric construction:
the uniform bound is as strong as the conclusion at the
level of existence quantifiers.

No diary Ramsey, genericity, finite flip absorption, or
unconditional countable-source flip property is used.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {DH : RoleDiary H}
variable {F : Nat → Nat}

/-- Every genuine coherent finite-support family already supplies
one admissible stage at each level with the identical finite-support
map. In particular its prescribed leaf-range certificate is kept. -/
theorem CoherentCofinalDiarySupportMaps.toAdmissibleStage
    (P : CoherentCofinalDiarySupportMaps DH K)
    (hRange : ∀ m u : Nat,
      u ∈ countableDiaryFiniteSupport H m →
      IsLeaf H u → ∃ t : Nat, P.map m u = F t)
    (m : Nat) :
    AdmissibleCofinalDiaryStage H K F m (P.map m) where
  ordered := by
    intro u v hu hv huv
    exact P.ordered m u v hu hv huv
  marker_zero := P.marker_zero m
  marker_one := P.marker_one m
  marker_two := P.marker_two m
  leaf_role := by
    intro u hu hLeaf
    exact P.leaf_role m u hu hLeaf
  one_split_role := by
    intro u hu hOne
    exact P.one_split_role m u hu hOne
  two_split_role := by
    intro u hu hTwo
    exact P.two_split_role m u hu hTwo
  induced_edge := by
    intro a b c ha hb hc hab hbc
    exact P.induced_edge m a b c ha hb hc hab hbc
  leaf_oneMeet := by
    intro a b ha hb hLa hLb
    exact P.leaf_oneMeet m a b ha hb hLa hLb
  leaf_twoMeet := by
    intro a b c d ha hb hc hd hab hcd hLa hLb hLc hLd
    exact P.leaf_twoMeet m a b c d ha hb hc hd hab hcd
      hLa hLb hLc hLd
  leaf_range := by
    intro u hu hLeaf
    exact hRange m u hu hLeaf

/-- Precise iff statement for the fixed target K and target leaf
range F: a coherent countable family of genuine admissible maps
exists if and only if there is ONE bound cap(u) such that at
EVERY finite stage SOME (possibly unrelated) admissible map
has all supported image values strictly below cap(u).

The forward direction uses the actual coherent limit as cap.
The backward direction is the previously verified finite-front
compactness theorem.

This result does not prove either side unconditionally. -/
theorem exists_coherentStages_iff_uniform_pointwise_bounds
    (DH : RoleDiary H) (K : Ordered3Graph Nat)
    (F : Nat → Nat) :
    (∃ P : CoherentCofinalDiarySupportMaps DH K,
      ∀ m u : Nat,
        u ∈ countableDiaryFiniteSupport H m →
        IsLeaf H u → ∃ t : Nat, P.map m u = F t) ↔
    (∃ cap : Nat → Nat,
      ∀ m : Nat,
        ∃ f : Nat → Nat,
          AdmissibleCofinalDiaryStage H K F m f ∧
          (∀ u : Nat, u ∈ countableDiaryFiniteSupport H m →
            f u < cap u)) := by
  classical
  constructor
  · rintro ⟨P,hRange⟩
    refine ⟨fun u => P.limit u + 1, ?_⟩
    intro m
    refine ⟨P.map m, P.toAdmissibleStage hRange m, ?_⟩
    intro u hu
    have hImage : P.limit u = P.map m u :=
      P.limit_eq_stage m u hu
    omega
  · rintro ⟨cap,hEvery⟩
    let front : FiniteCofinalDiaryFronts DH K F :=
      finiteDiaryFronts_of_pointwiseBounds DH F cap hEvery
    obtain ⟨P,hRange⟩ := front.toCertified.exists_coherent
    exact ⟨P,hRange⟩

end DiaryLeafPriority
end ThreeUniformDiaries
