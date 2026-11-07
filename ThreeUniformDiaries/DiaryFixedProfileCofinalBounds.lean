import ThreeUniformDiaries.DiaryFixedProfileUniformBoundCriterion

/-!
# Cofinal finite horizons suffice for persistent fixed-profile next-leaf choices

The verified quantitative criterion in DiaryFixedProfileUniformBoundCriterion
requires a single bound B with a compatible reserved realization of a
PRESCRIBED complete new nonleaf profile at EVERY exact horizon n.

A weaker-looking condition is in fact equivalent: for every requested
horizon N, find SOME horizon n >= N with a compatible realization,
using the same uniform B and the same fixed profile.

Actual reserved diary stages restrict to earlier finite leaf-meet
supports without changing any image values. Therefore each such late
witness also satisfies the earlier horizon obligation.

This avoids the stronger demand of building a witness separately at
each prescribed horizon when a geometric tail construction naturally
supplies a cofinal sequence of horizons. It still assumes a UNIFORM
BOUND and does not rule out escape or prove countable diary
unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The complete split profile p and old support f are fixed,
and the next leaf image has ONE uniform bound B along arbitrarily
late finite horizons. Witnesses at different horizons may differ. -/
def HasCofinalBoundedNextLeafWithFixedProfile
    (H K : Ordered3Graph Nat) (F f : Nat → Nat) (m : Nat)
    (p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat)) :
    Prop :=
  ∃ B : Nat, ∀ N : Nat, ∃ n : Nat, N ≤ n ∧
    ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1 + n) g ∧
      CofinalDiaryStageCompatible H m f g ∧
      (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
        g u.val = p u) ∧
      g m ≤ B

/-- A fixed complete nonleaf profile with one image bound along a
COFINAL set of finite horizons already has a bounded realization
at EVERY exact finite horizon, thanks to genuine stage restriction.
The converse uses n=N. No infinite branch is assumed. -/
theorem fixedProfile_uniformBound_iff_cofinalBounded
    (H K : Ordered3Graph Nat) (F f : Nat → Nat) (m : Nat)
    (p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat)) :
    HasUniformNextLeafBoundWithFixedProfile H K F f m p ↔
      HasCofinalBoundedNextLeafWithFixedProfile H K F f m p := by
  constructor
  · rintro ⟨B, hEvery⟩
    refine ⟨B, ?_⟩
    intro N
    obtain ⟨g, Q, hOld, hp, hBound⟩ := hEvery N
    exact ⟨N, le_rfl, g, Q, hOld, hp, hBound⟩
  · rintro ⟨B, hCofinal⟩
    refine ⟨B, ?_⟩
    intro N
    obtain ⟨n, hNn, g, Q, hOld, hp, hBound⟩ :=
      hCofinal N
    have hQ : ReservedDiaryStage H K F (m + 1 + N) g :=
      Q.restrict (by omega)
    exact ⟨g, hQ, hOld, hp, hBound⟩

/-- At a genuine source leaf, the existence of a PERSISTENT
compatible next-leaf stage with precisely profile p is equivalent
to finding bounded p-witnesses at ARBITRARILY LARGE horizons.
No fresh bound needs to be chosen at every horizon. -/
theorem persistent_fixedProfile_iff_cofinal_bounded
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat)) :
    HasPersistentNextLeafWithFixedProfile H K F f m p ↔
      HasCofinalBoundedNextLeafWithFixedProfile H K F f m p :=
  (persistent_fixedProfile_iff_uniform_nextLeaf_bound hm p).trans
    (fixedProfile_uniformBound_iff_cofinalBounded H K F f m p)

/-- This is the index-bound formulation for cofinal horizons:
an UNIFORM finite bound T on one chosen index t with g(m)=F(t)
suffices even when F is unordered or noninjective. -/
theorem persistent_fixedProfile_of_cofinal_bounded_index
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat))
    (hIndex : ∃ T : Nat, ∀ N : Nat, ∃ n : Nat, N ≤ n ∧
      ∃ g : Nat → Nat,
        ReservedDiaryStage H K F (m + 1 + n) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
          g u.val = p u) ∧
        ∃ t : Nat, t < T ∧ g m = F t) :
    HasPersistentNextLeafWithFixedProfile H K F f m p := by
  classical
  obtain ⟨T, hCofinal⟩ := hIndex
  apply (persistent_fixedProfile_iff_cofinal_bounded hm p).mpr
  refine ⟨(Finset.range T).sup F, ?_⟩
  intro N
  obtain ⟨n, hNn, g, Q, hOld, hp, t, ht, hEq⟩ :=
    hCofinal N
  refine ⟨n, hNn, g, Q, hOld, hp, ?_⟩
  rw [hEq]
  exact Finset.le_sup (f := F) (Finset.mem_range.mpr ht)

end DiaryLeafPriority
end ThreeUniformDiaries
