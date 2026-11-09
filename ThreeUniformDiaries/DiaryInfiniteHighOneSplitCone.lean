import ThreeUniformDiaries.DiaryMonochromaticLeafMeetObstruction
import ThreeUniformDiaries.DiarySingletonColourCofinalCone

/-!
# Track D: infinite high one-split cone inside every injected genuine leaf range

The checked Track C high-meet theorem gives two late prescribed
leaves whose singleton meet is an arbitrarily high genuine one-split.

This strengthens that positive ingredient: for EVERY finite
target cut B, numerical lower bound M, and source-index bound N,
there is an infinite, strictly source-index-increasing sequence
of leaves in the SAME original injected prescribed range such that
* all target leaf images exceed M and B;
* ALL the leaves have exactly the SAME complete mixed singleton
  colour below B, including nonedge tests;
* EVERY distinct pair of these leaves has a genuine one-split meet
  at numerical target index at least B.

The proof is finite palette recurrence plus finite-preimage escape,
followed by recursively selecting later indices. There is NO
claim that the chosen sequence forms an induced generic subcopy,
that it realizes a prescribed old-stage mixed type, or that a
particular old supported map extends; the pairwise meet indices
need not be equal or satisfy any prescribed quantitative reserve.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every injected infinite range of genuine leaves in a full diary
contains a countably infinite chosen sequence of leaves that is
monochromatic for the COMPLETE mixed singleton-type mask below
an arbitrary finite cut B. Every pair has an actual S1 one-split
meet at least B.

The input cutoff N and image cutoff M are arbitrary, and the
original outer map F is not assumed to preserve the enumeration
order. This is a genuine positive consequence of the full
RoleDiary axioms, not a relative-extension theorem. -/
theorem RoleDiary.exists_infinite_high_oneSplit_cone
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (F : Nat → Nat) (hInjective : Function.Injective F)
    (hLeaves : ∀ n : Nat, IsLeaf K (F n))
    (B M N : Nat) :
    ∃ (indices : Nat → Nat),
      StrictMono indices ∧
      (∀ k : Nat, N ≤ indices k ∧
        M < F (indices k) ∧
        B ≤ F (indices k)) ∧
      (∀ i j : Nat, i < j →
        DiaryLowerBoundColors.singletonColour K B (F (indices i)) =
          DiaryLowerBoundColors.singletonColour K B (F (indices j)) ∧
        IsOneSplit K
          (K.oneMeetLevel (F (indices i)) (F (indices j))) ∧
        B ≤ K.oneMeetLevel (F (indices i)) (F (indices j))) := by
  classical
  obtain ⟨c, hRecur⟩ :=
    exists_cofinal_existing_singletonColour K B F
  obtain ⟨Nlarge, hLarge⟩ :=
    injective_nat_eventually_above_bound F hInjective (max B M)
  let start := max N Nlarge
  let pick : Nat → Nat := fun n =>
    Classical.choose (hRecur n)
  have hPick (n : Nat) :
      n ≤ pick n ∧
      DiaryLowerBoundColors.singletonColour K B (F (pick n)) = c := by
    exact Classical.choose_spec (hRecur n)
  let indices : Nat → Nat :=
    Nat.rec (pick start) (fun _ prev => pick (prev + 1))
  have hStep (k : Nat) : indices k < indices (k + 1) := by
    change indices k < pick (indices k + 1)
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (hPick (indices k + 1)).1
  have hMono : StrictMono indices :=
    strictMono_nat_of_lt_succ hStep
  have hAbove (k : Nat) : start ≤ indices k := by
    induction k with
    | zero =>
        change start ≤ pick start
        exact (hPick start).1
    | succ k ih =>
        exact ih.trans (hStep k).le
  have hColour (k : Nat) :
      DiaryLowerBoundColors.singletonColour K B (F (indices k)) = c := by
    cases k with
    | zero =>
        change DiaryLowerBoundColors.singletonColour K B
          (F (pick start)) = c
        exact (hPick start).2
    | succ k =>
        change DiaryLowerBoundColors.singletonColour K B
          (F (pick (indices k + 1))) = c
        exact (hPick (indices k + 1)).2
  have hTarget (k : Nat) : max B M < F (indices k) :=
    hLarge (indices k) (le_trans (le_max_right N Nlarge) (hAbove k))
  refine ⟨indices, hMono, ?_, ?_⟩
  · intro k
    constructor
    · exact (le_max_left N Nlarge).trans (hAbove k)
    constructor
    · exact lt_of_le_of_lt (le_max_right B M) (hTarget k)
    · exact le_of_lt (lt_of_le_of_lt (le_max_left B M) (hTarget k))
  · intro i j hij
    have hEqual :
        DiaryLowerBoundColors.singletonColour K B (F (indices i)) =
          DiaryLowerBoundColors.singletonColour K B (F (indices j)) := by
      exact (hColour i).trans (hColour j).symm
    have hNe : F (indices i) ≠ F (indices j) := by
      intro h
      have hEq : indices i = indices j := hInjective h
      exact (ne_of_lt (hMono hij)) hEq
    have hRole : IsOneSplit K
        (K.oneMeetLevel (F (indices i)) (F (indices j))) :=
      DK.singleton_meets _ _ (hLeaves _) (hLeaves _) hNe
    have hLower :
        B ≤ K.oneMeetLevel (F (indices i)) (F (indices j)) :=
      equal_singletonColour_forces_oneMeet_ge_cut K B
        (F (indices i)) (F (indices j))
        (le_of_lt (lt_of_le_of_lt (le_max_left B M) (hTarget i)))
        (le_of_lt (lt_of_le_of_lt (le_max_left B M) (hTarget j)))
        hEqual
    exact ⟨hEqual, hRole, hLower⟩

end DiaryLeafPriority
end ThreeUniformDiaries
