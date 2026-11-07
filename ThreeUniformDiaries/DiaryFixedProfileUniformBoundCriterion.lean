import ThreeUniformDiaries.DiaryFixedFullSplitProfileEscape

/-!
# Track C/D: uniform next-leaf bounds exactly characterize persistence
  inside one prescribed complete full split-generator profile.

The full split record p is fixed at ALL finite horizons, and
all finite maps agree with the prescribed old support map f.
No compatible infinite family or countable source embedding is assumed.

This iff is a quantitative restatement of the genuine escape
obstruction. It does NOT provide the required uniform bound
from genericity or from finite diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A single persistent next-leaf map with precisely the
specified COMPLETE new nonleaf-generator image record. -/
def HasPersistentNextLeafWithFixedProfile
    (H K : Ordered3Graph Nat) (F f : Nat → Nat) (m : Nat)
    (p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat)) :
    Prop :=
  ∃ g : Nat → Nat,
    PersistentReservedDiaryStage H K F (m + 1) g ∧
    CofinalDiaryStageCompatible H m f g ∧
    ∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
      g u.val = p u

/-- A uniform numerical bound on SOME actual next-leaf image
at every finite horizon while the entire split record p and
every OLD supported image stay fixed. Different horizons may
use different maps. -/
def HasUniformNextLeafBoundWithFixedProfile
    (H K : Ordered3Graph Nat) (F f : Nat → Nat) (m : Nat)
    (p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat)) :
    Prop :=
  ∃ B : Nat, ∀ n : Nat, ∃ g : Nat → Nat,
    ReservedDiaryStage H K F (m + 1 + n) g ∧
    CofinalDiaryStageCompatible H m f g ∧
    (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
      g u.val = p u) ∧
    g m ≤ B

/-- At a true new source leaf the two conditions are EQUIVALENT,
without an extra assumption that p is already realized at
each horizon: that follows from either side.

Forward direction preserves old images and all new split
generators by compatibility on S_(m+1). Reverse direction
excludes the nonvacuous fixed-profile escape alternative from
the verified full-profile dichotomy. -/
theorem persistent_fixedProfile_iff_uniform_nextLeaf_bound
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat)) :
    HasPersistentNextLeafWithFixedProfile H K F f m p ↔
      HasUniformNextLeafBoundWithFixedProfile H K F f m p := by
  classical
  constructor
  · rintro ⟨g0, P0, hOld0, hp0⟩
    refine ⟨g0 m, ?_⟩
    intro n
    obtain ⟨gN, QN, hCompat⟩ := P0.2 n
    have hOldN : CofinalDiaryStageCompatible H m f gN := by
      intro u hu
      have huNext : u ∈ countableDiaryFiniteSupport H (m + 1) :=
        countableDiaryFiniteSupport_mono H m (m + 1) (by omega) hu
      exact (hCompat u huNext).trans (hOld0 u hu)
    have hpN :
        ∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
          gN u.val = p u := by
      intro u
      have huNext : u.val ∈ countableDiaryFiniteSupport H (m + 1) :=
        ((mem_newNonleafGeneratorSupport_iff H m u.val).mp u.property).1
      exact (hCompat u.val huNext).trans (hp0 u)
    have hmNext : m ∈ countableDiaryFiniteSupport H (m + 1) := by
      exact mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H (m + 1)) m
        ((mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
          ⟨hm.1, by omega, hm⟩)
    refine ⟨gN, QN, hOldN, hpN, ?_⟩
    rw [hCompat m hmNext]
  · rintro ⟨B, hBound⟩
    have hEvery :
        ∀ n : Nat, HasFixedNonleafProfileHorizon H K F f m p n := by
      intro n
      obtain ⟨g, Q, hOld, hp, _⟩ := hBound n
      exact ⟨g, Q, hOld, hp⟩
    rcases fixedNonleafProfile_persistent_successor_or_escape
        hm p hEvery with hGood | hEscape
    · exact hGood
    · obtain ⟨n, _, hAll⟩ := hEscape B
      obtain ⟨g, Q, hOld, hp, hSmall⟩ := hBound n
      exact False.elim ((not_lt_of_ge hSmall) (hAll g Q hOld hp))

/-- A bound on PREIMAGE INDICES in the prescribed leaf range F
is sufficient, even when F is not increasing: only a finite
collection F[0..B) of possible new images is involved. -/
theorem persistent_fixedProfile_of_bounded_preimage_index
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat))
    (hIndex : ∃ B : Nat, ∀ n : Nat, ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1 + n) g ∧
      CofinalDiaryStageCompatible H m f g ∧
      (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
        g u.val = p u) ∧
      ∃ t : Nat, t < B ∧ g m = F t) :
    HasPersistentNextLeafWithFixedProfile H K F f m p := by
  classical
  obtain ⟨B, hAll⟩ := hIndex
  apply (persistent_fixedProfile_iff_uniform_nextLeaf_bound hm p).mpr
  refine ⟨(Finset.range B).sup F, ?_⟩
  intro n
  obtain ⟨g, Q, hOld, hp, t, ht, hEq⟩ := hAll n
  refine ⟨g, Q, hOld, hp, ?_⟩
  rw [hEq]
  exact Finset.le_sup (f := F) (Finset.mem_range.mpr ht)

end DiaryLeafPriority
end ThreeUniformDiaries
