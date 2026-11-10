import ThreeUniformDiaries.DiaryExactSingletonColourSplitCut
import ThreeUniformDiaries.DiaryPersistentSuccessorBoundEquivalence

/-!
# Track A: one FINITE cut isolates each genuine leaf; realized recurring virtual
  singleton types force persistent next-leaf successors

In a full RoleDiary target, the exact S1 colour cutoff says that two
distinct true leaves have equal mixed singleton colours below B
exactly when B is at most their S1 one-meet. Since the S1 meet is an
actual one-split and a true leaf is not a split, oneMeet(u,v)<u for
every distinct true leaf v. Thus the finite complete mixed singleton
mask of u at cut u singles out u among ALL genuine target leaves.

This gives a direct, noncompactness-free lemma: if compatible reserved
finite-horizon extensions cofinally realize the SAME mixed singleton
colour as a particular target leaf u at cut u, every such horizon's
new source leaf is literally mapped to u. The uniform numerical
next-leaf bound u and existing finite-choice successor theorem then
produce one persistent reserved successor fixing the old support.

In particular a cofinally recurrent all-cut virtual singleton type
that is REALIZED by a genuine target leaf implies a persistent next
source leaf. This is a sufficient criterion, not a proof that any
escaping virtual type is realized. The full target diary can genuinely
omit those types. No unconditional diary unavoidability is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A genuine diary leaf u is isolated among genuine leaves by the
FINITELY MANY complete mixed singleton-colour tests below cut u.
This is stronger than uniqueness of a whole countable mixed type. -/
theorem RoleDiary.singletonColour_self_cut_isolates_leaf
    {K : Ordered3Graph Nat}
    (DK : RoleDiary K)
    (u v : Nat) (hu : IsLeaf K u) (hv : IsLeaf K v) :
    DiaryLowerBoundColors.singletonColour K u u =
      DiaryLowerBoundColors.singletonColour K u v ↔ u = v := by
  constructor
  · intro hColour
    by_contra hNe
    have hSplit : IsOneSplit K (K.oneMeetLevel u v) :=
      DK.singleton_meets u v hu hv hNe
    have hCap : K.oneMeetLevel u v ≤ u :=
      (K.oneMeetLevel_le_min u v).trans (min_le_left _ _)
    have hNotAtU : K.oneMeetLevel u v ≠ u := by
      intro hEq
      have hOneU : IsOneSplit K u := by
        simpa only [hEq] using hSplit
      exact hu.2.1 hOneU.2.1
    have hStrict : K.oneMeetLevel u v < u := by omega
    have hBound : u ≤ K.oneMeetLevel u v :=
      (DK.singletonColour_eq_iff_cut_le_oneMeet
        hu hv hNe u).mp hColour
    omega
  · intro h
    rw [h]

/-- Cohesion of the *one finite exact leaf-isolating colour* at
cofinally many genuine old-compatible finite horizons forces one
numerically BOUNDED image for the next source leaf, hence a
finitely persistent compatible successor.

No assumption that the whole target range is monochromatic, or
that the target admits countable type saturation, is made. -/
theorem persistent_successor_of_cofinal_isolating_leaf_colour
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (DK : RoleDiary K)
    (hm : IsLeaf H m)
    (u : Nat) (hu : IsLeaf K u)
    (hRecur : ∀ N : Nat, ∃ n : Nat, N ≤ n ∧
      ∃ g : Nat → Nat,
        ReservedDiaryStage H K F (m + 1 + n) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        DiaryLowerBoundColors.singletonColour K u (g m) =
          DiaryLowerBoundColors.singletonColour K u u) :
    ∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g := by
  have hBound : HasCofinalBoundedNextLeafImages H K F f m := by
    refine ⟨u, ?_⟩
    intro N
    obtain ⟨n, hn, g, Q, hOld, hColour⟩ := hRecur N
    have hmSelected : m ∈ countableDiaryLeafPrefix H (m + 1 + n) :=
      (mem_countableDiaryLeafPrefix_iff H (m + 1 + n) m).mpr
        ⟨hm.1, by omega, hm⟩
    have hmSupported : m ∈ countableDiaryFiniteSupport H (m + 1 + n) :=
      mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H (m + 1 + n)) m hmSelected
    have hTargetLeaf : IsLeaf K (g m) :=
      Q.1.leaf_role m hmSupported hm
    have hEq : u = g m :=
      (DK.singletonColour_self_cut_isolates_leaf
        u (g m) hu hTargetLeaf).mp hColour.symm
    refine ⟨n, hn, g, Q, hOld, ?_⟩
    omega
  exact (persistentSuccessor_iff_cofinalBoundedNextLeafImages hm).mpr
    hBound

/-- The critical-path implication: if an all-cut virtual mixed
singleton type recurs cofinally in ACTUAL compatible finite reserved
horizons and is realized by a genuine target leaf u, then one
compatible persistent new leaf exists.

Only the finite mask at cut u is used. No virtual-type coherence
axiom is needed, and the theorem does not assert type realization
from finite recurrence or countable universality. -/
theorem persistent_successor_of_realized_cofinal_virtual_singleton_type
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (DK : RoleDiary K)
    (hm : IsLeaf H m)
    (c : (B : Nat) → Fin B → Fin B → Bool)
    (hRecur : ∀ B N : Nat, ∃ n : Nat, N ≤ n ∧
      ∃ g : Nat → Nat,
        ReservedDiaryStage H K F (m + 1 + n) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        DiaryLowerBoundColors.singletonColour K B (g m) = c B)
    (u : Nat) (hu : IsLeaf K u)
    (hRealized : ∀ B : Nat,
      DiaryLowerBoundColors.singletonColour K B u = c B) :
    ∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g := by
  apply persistent_successor_of_cofinal_isolating_leaf_colour DK hm u hu
  intro N
  obtain ⟨n, hn, g, Q, hOld, hColour⟩ := hRecur u N
  refine ⟨n, hn, g, Q, hOld, ?_⟩
  exact hColour.trans (hRealized u).symm

end DiaryLeafPriority
end ThreeUniformDiaries
