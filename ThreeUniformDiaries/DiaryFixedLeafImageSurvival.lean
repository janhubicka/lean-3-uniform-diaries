import ThreeUniformDiaries.DiaryPersistentSuccessorBoundEquivalence

/-!
# Track C: fixed next-leaf image survival and finite death certificates

English proof and independent adversarial audit:
  janhubicka/3-uniform-diaries PR #265
  notes/track_c_fixed_value_survival_finite_exclusion_20261108.md

For a GENUINE new source leaf m, a finitely persistent compatible
next-stage map exists iff ONE fixed numerical next-leaf image v
occurs in genuine old-compatible reserved stages at EVERY finite
continuation horizon. This is the singleton instance of the already
verified finite next-image cover theorem; no separate countable
compactness or monotonicity of the prescribed leaf map F is assumed.

Consequently, no persistent successor exists iff EVERY fixed proposed
image v dies at SOME finite horizon. The finite maximum of these
death horizons excludes ANY fixed finite image set at ALL later
horizons. The escape may be vacuous without an old persistent stage.
Nothing here establishes unconditional diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A SINGLE prescribed numerical image v of the next source leaf
has a genuine old-S_m-compatible reserved realization at EVERY
finite horizon after selecting m. The realizing total maps may vary
with the horizon; no global branch is presupposed. -/
def FixedNextLeafImageAtAllHorizons
    (H K : Ordered3Graph Nat) (F f : Nat → Nat)
    (m v : Nat) : Prop :=
  ∀ n : Nat, ∃ g : Nat → Nat,
    ReservedDiaryStage H K F (m + 1 + n) g ∧
    CofinalDiaryStageCompatible H m f g ∧
    g m = v

/-- The exact single-leaf-value criterion for persistence. New
nonleaf S1/S2 generator images are fixed by the old selected
leaves plus the new image v, via the verified finite-cover lemma.
This does NOT construct such a v from genericity. -/
theorem persistentSuccessor_iff_fixedImageAllHorizons
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m) :
    (∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g) ↔
      ∃ v : Nat, FixedNextLeafImageAtAllHorizons H K F f m v := by
  classical
  constructor
  · rintro ⟨g0, P0, hOld0⟩
    refine ⟨g0 m, ?_⟩
    intro n
    obtain ⟨gN, QN, hCompat⟩ := P0.2 n
    have hOldN : CofinalDiaryStageCompatible H m f gN :=
      CofinalDiaryStageCompatible.trans (Nat.le_succ m) hOld0 hCompat
    have hM : m ∈ countableDiaryFiniteSupport H (m + 1) :=
      mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H (m + 1)) m
        ((mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
          ⟨hm.1, by omega, hm⟩)
    exact ⟨gN, QN, hOldN, hCompat m hM⟩
  · rintro ⟨v, hAll⟩
    apply exists_persistent_reserved_successor_of_finite_cover hm
    refine ⟨{v}, ?_⟩
    intro n
    obtain ⟨g, Q, hOld, hVal⟩ := hAll n
    exact ⟨g, Q, hOld, Finset.mem_singleton.mpr hVal⟩

/-- Every numerical next-leaf candidate has a finite death horizon
iff no old-compatible finitely persistent successor exists. This is
classical quantifier duality AFTER the genuine singleton compactness
result, and has no hidden nonemptiness assumption on horizon fibres. -/
theorem noPersistentSuccessor_iff_everyValueHasFiniteDeath
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m) :
    (¬ ∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g) ↔
      (∀ v : Nat, ∃ n : Nat, ∀ g : Nat → Nat,
        ReservedDiaryStage H K F (m + 1 + n) g →
        CofinalDiaryStageCompatible H m f g →
        g m ≠ v) := by
  classical
  constructor
  · intro hNo v
    by_contra hNoDeath
    have hAll : FixedNextLeafImageAtAllHorizons H K F f m v := by
      intro n
      by_contra hNoWitness
      apply hNoDeath
      refine ⟨n, ?_⟩
      intro g Q hOld hEq
      exact hNoWitness ⟨g, Q, hOld, hEq⟩
    exact hNo ((persistentSuccessor_iff_fixedImageAllHorizons hm).mpr
      ⟨v, hAll⟩)
  · intro hDeaths hSucc
    obtain ⟨v, hAll⟩ :=
      (persistentSuccessor_iff_fixedImageAllHorizons hm).mp hSucc
    obtain ⟨n, hDeath⟩ := hDeaths v
    obtain ⟨g, Q, hOld, hEq⟩ := hAll n
    exact (hDeath g Q hOld) hEq

/-- The strongest purely FINITE obstruction formulation:
no persistent compatible successor iff EVERY finite set of possible
target leaf images is uniformly excluded at all sufficiently long
horizons, while retaining the literal old support map.

The exclusion may be vacuous if there are no late stages. If the
old stage is finitely persistent, existing theorems separately
supply genuine nonempty witnesses at every horizon. -/
theorem noPersistentSuccessor_iff_eventuallyAvoidsEveryFiniteImageSet
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m) :
    (¬ ∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g) ↔
      (∀ W : Finset Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
        ∀ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g →
          CofinalDiaryStageCompatible H m f g →
          g m ∉ W) := by
  classical
  constructor
  · intro hNo W
    have hDeaths :=
      (noPersistentSuccessor_iff_everyValueHasFiniteDeath hm).mp hNo
    let death : Nat → Nat := fun v => Classical.choose (hDeaths v)
    let N : Nat := W.sup death
    refine ⟨N, ?_⟩
    intro n hn g Q hOld hMem
    have hDeathBound : death (g m) ≤ N :=
      Finset.le_sup (f := death) hMem
    have hSmallStage :
        ReservedDiaryStage H K F (m + 1 + death (g m)) g :=
      Q.restrict (by omega)
    have hExcluded :=
      Classical.choose_spec (hDeaths (g m))
    exact (hExcluded g hSmallStage hOld) rfl
  · intro hAvoid
    apply (noPersistentSuccessor_iff_everyValueHasFiniteDeath hm).mpr
    intro v
    obtain ⟨N, hAll⟩ := hAvoid ({v} : Finset Nat)
    refine ⟨N, ?_⟩
    intro g Q hOld hEq
    have hNotMem : g m ∉ ({v} : Finset Nat) :=
      hAll N (le_refl N) g Q hOld
    exact hNotMem (Finset.mem_singleton.mpr hEq)

end DiaryLeafPriority
end ThreeUniformDiaries
