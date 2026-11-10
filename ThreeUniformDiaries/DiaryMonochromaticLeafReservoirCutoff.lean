import ThreeUniformDiaries.DiaryExactSingletonColourSplitCut

/-!
# Track A: exact numerical gate for monochromatic diary-leaf reservoirs

For an injective list F of genuine leaves of a full role diary K, all
leaves in F[Nat] have ONE complete mixed singleton colour below B if
and only if EVERY pair of leaves in the same range has an S1 meet
at least B.  This is an exact equivalence, not merely one direction.

In particular there is a concrete upper bound on all cuts at which
the FIXED range is monochromatic: the one-meet of F(0) and F(1).
No ONE range containing those two leaves can be monochromatic at
arbitrarily large finite cuts.

This is an adversarial regression against a naive diagonal fusion
which repeatedly chooses monochromatic subcopies at increasing cuts
but insists that all previously selected leaves remain IN every
new monochromatic reservoir. Such a strategy must instead store the
old images separately and protect their mixed incidence/meet data.
This result does not construct a new-leaf persistent successor,
a relative Safe subsystem, or countable diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Exact cutoff criterion for a fixed INJECTED infinite range of true
target leaves to be monochromatic for the complete mixed singleton
colour below B. No order assumption on F. -/
theorem RoleDiary.monochromatic_leaf_range_iff_pairwise_oneMeet_ge
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (F : Nat → Nat) (hInjective : Function.Injective F)
    (hLeaves : ∀ i : Nat, IsLeaf K (F i))
    (B : Nat) :
    (∃ c : Fin B → Fin B → Bool,
        ∀ i : Nat,
          DiaryLowerBoundColors.singletonColour K B (F i) = c) ↔
      (∀ i j : Nat, i < j →
        B ≤ K.oneMeetLevel (F i) (F j)) := by
  classical
  constructor
  · rintro ⟨c, hColour⟩ i j hij
    have hNe : F i ≠ F j := by
      intro he
      exact (ne_of_lt hij) (hInjective he)
    have hEq :
        DiaryLowerBoundColors.singletonColour K B (F i) =
          DiaryLowerBoundColors.singletonColour K B (F j) :=
      (hColour i).trans (hColour j).symm
    exact (DK.singletonColour_eq_iff_cut_le_oneMeet
      (hLeaves i) (hLeaves j) hNe B).mp hEq
  · intro hPairs
    refine ⟨DiaryLowerBoundColors.singletonColour K B (F 0), ?_⟩
    intro i
    by_cases hi : i = 0
    · subst i
      rfl
    · have hPos : 0 < i := by omega
      have hNe : F 0 ≠ F i := by
        intro he
        exact hi ((hInjective he).symm)
      have hEq :
          DiaryLowerBoundColors.singletonColour K B (F 0) =
            DiaryLowerBoundColors.singletonColour K B (F i) :=
        (DK.singletonColour_eq_iff_cut_le_oneMeet
          (hLeaves 0) (hLeaves i) hNe B).mpr
          (hPairs 0 i hPos)
      exact hEq.symm

/-- The first two distinct target leaves of the range impose a
FINITE upper bound on the monochromatic cut of the whole range.
It is not possible to refine a single range to monochromatic
arbitrarily high cuts while retaining both old leaves. -/
theorem RoleDiary.monochromatic_leaf_range_cut_le_first_meet
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (F : Nat → Nat) (hInjective : Function.Injective F)
    (hLeaves : ∀ i : Nat, IsLeaf K (F i))
    (B : Nat)
    (hMono : ∃ c : Fin B → Fin B → Bool,
      ∀ i : Nat,
        DiaryLowerBoundColors.singletonColour K B (F i) = c) :
    B ≤ K.oneMeetLevel (F 0) (F 1) := by
  have hPairs :=
    (DK.monochromatic_leaf_range_iff_pairwise_oneMeet_ge
      F hInjective hLeaves B).mp hMono
  exact hPairs 0 1 (by omega)

/-- There is NO single injected genuine-leaf range monochromatic
at all finite mixed singleton-type cuts, even though a DIFFERENT
infinite high-meet subrange exists for each individual cut B.
This is a no-go for globally nested monochromatization that
retains two fixed previously chosen leaves. -/
theorem RoleDiary.not_all_cut_monochromatic_leaf_range
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (F : Nat → Nat) (hInjective : Function.Injective F)
    (hLeaves : ∀ i : Nat, IsLeaf K (F i)) :
    ¬ (∀ B : Nat, ∃ c : Fin B → Fin B → Bool,
      ∀ i : Nat,
        DiaryLowerBoundColors.singletonColour K B (F i) = c) := by
  intro hAll
  let B := K.oneMeetLevel (F 0) (F 1) + 1
  have hBound : B ≤ K.oneMeetLevel (F 0) (F 1) :=
    DK.monochromatic_leaf_range_cut_le_first_meet
      F hInjective hLeaves B (hAll B)
  dsimp [B] at hBound
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
