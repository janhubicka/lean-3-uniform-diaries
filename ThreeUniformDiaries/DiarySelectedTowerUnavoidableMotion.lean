import ThreeUniformDiaries.DiaryNoLiteralFiniteFullDiaryEndExtension
import ThreeUniformDiaries.DiarySelectedConditionalFullRoleDiary

/-!
# Track B: any proper finite full-diary tower extension must move an old rank

The verified no-proper-literal-end-extension theorem makes a strong
NEGATIVE restriction on selecting the finite strong-absorber tower:
if a chosen bounded meet embedding B_n -> B_(n+1) increases the
finite frame size, it MUST move at least one actual old frame vertex.

Unbounded selected frame sizes force infinitely late such motions.
Conditionally on bounded forward ranks, their *positions* must
eventually lie above each prescribed finite cut: a finite-injury
moving frontier, NOT literal growth of full finite diaries.

A crucial adversarial warning: movement only at increasingly high
individual stage indices does NOT imply bounded forward ranks.
The already verified frozen-prefix escape tower gives a
counterexample; the missing requirement remains EVENTUAL CAPTURE
of every old vertex by a permanently protected front.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A genuinely proper bounded embedding between full finite
diaries CANNOT fix every old source rank. Otherwise the old
full finite diary would be a literal induced initial prefix
of the larger full finite diary, which has been disproved. -/
theorem finiteFullDiary_properEmbedding_moves_old_rank
    {A C : Ordered3Graph Nat} {n m : Nat} {f : Nat → Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (DC : FiniteRoleDiaryBlock C m)
    (hn : 4 ≤ n) (hGrow : n < m)
    (E : FiniteBoundedMeetEmbedding A C n m f) :
    ∃ u : Nat, u < n ∧ f u ≠ u := by
  by_contra hNot
  have hFixed : ∀ u : Nat, u < n → f u = u := by
    intro u hu
    by_contra hMove
    exact hNot ⟨u,hu,hMove⟩
  have hInd : ∀ a b c : Nat, a < b → b < c → c < n →
      (A.edge a b c ↔ C.edge a b c) := by
    intro a b c hab hbc hc
    have ha : a < n := by omega
    have hb : b < n := by omega
    have he := E.toMeetEmbedding.edge_iff a b c hab hbc hc
    rw [hFixed a ha,hFixed b hb,hFixed c hc] at he
    exact he.symm
  have heq := no_proper_full_diary_end_extension_of_induced_prefix
    DA DC hn (by omega : n ≤ m) hInd
  omega

/-- An actual selected strong-absorber successor which makes
the target finite frame larger must move some true old vertex.
Its first three markers remain fixed; hence this is genuinely
an old nonmarker movement. -/
theorem selectedAbsorberTower_properGrowth_moves_old_rank
    (n : Nat)
    (hGrow :
      (universalStrongAbsorberTower n).bound <
        (universalStrongAbsorberTower (n+1)).bound) :
    ∃ u : Nat,
      3 ≤ u ∧ u < (universalStrongAbsorberTower n).bound ∧
      universalStrongAbsorberTower_stepMap n u ≠ u := by
  have hSize := selectedAbsorberFiniteOrderTower.size_mono
    0 n (Nat.zero_le n)
  have hfour : 4 ≤ (universalStrongAbsorberTower n).bound := by
    change 4 ≤ (universalStrongAbsorberTower n).bound at hSize
    exact hSize
  obtain ⟨u,hu,hMove⟩ :=
    finiteFullDiary_properEmbedding_moves_old_rank
      (universalStrongAbsorberTower n).diary
      (universalStrongAbsorberTower (n+1)).diary
      hfour hGrow (universalStrongAbsorberTower_stepMap_spec n)
  have hu3 : 3 ≤ u := by
    by_contra hlt
    have hMarker : u = 0 ∨ u = 1 ∨ u = 2 := by omega
    have E := (universalStrongAbsorberTower_stepMap_spec n).toMeetEmbedding
    rcases hMarker with h0 | h1 | h2
    · subst u
      exact hMove E.marker_zero
    · subst u
      exact hMove E.marker_one
    · subst u
      exact hMove E.marker_two
  exact ⟨u,hu3,hu,hMove⟩

namespace FiniteOrderTransitionTower

/-- An increasing tower of finite linear-order frames with
unbounded sizes must have strict size growth at arbitrarily late
stages. This does not use diary axioms or bounded ranks. -/
theorem exists_proper_growth_after
    (T : FiniteOrderTransitionTower)
    (hUnbounded : ∀ R : Nat, ∃ j : Nat, R < T.size j)
    (N : Nat) :
    ∃ n : Nat, N ≤ n ∧ T.size n < T.size (n+1) := by
  by_contra hNo
  have hNever : ∀ n : Nat, N ≤ n →
      T.size (n+1) ≤ T.size n := by
    intro n hn
    have hNotStrict : ¬ T.size n < T.size (n+1) := by
      intro hs
      exact hNo ⟨n,hn,hs⟩
    omega
  have hConstant : ∀ k : Nat, T.size (N+k) = T.size N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hMono := T.size_le_succ (N+k)
        have hBack := hNever (N+k) (by omega)
        have hEq : T.size ((N+k)+1) = T.size (N+k) := by omega
        calc
          T.size (N+(k+1)) = T.size ((N+k)+1) := by omega
          _ = T.size (N+k) := hEq
          _ = T.size N := ih
  obtain ⟨j,hBig⟩ := hUnbounded (T.size N)
  have hNj : N ≤ j := by
    by_contra h
    have hjN : j ≤ N := by omega
    have hMono := T.size_mono j N hjN
    omega
  have hEq := hConstant (j-N)
  have hIdx : N+(j-N) = j := by omega
  rw [hIdx] at hEq
  omega

end FiniteOrderTransitionTower

/-- The actual selected absorber tower has properly growing
finite frame stages arbitrarily far into the future. -/
theorem selectedAbsorberTower_exists_properGrowth_after
    (N : Nat) :
    ∃ n : Nat, N ≤ n ∧
      (universalStrongAbsorberTower n).bound <
        (universalStrongAbsorberTower (n+1)).bound := by
  have hUnbounded : ∀ R : Nat,
      ∃ j : Nat, R < selectedAbsorberFiniteOrderTower.size j := by
    intro R
    simpa only [selectedAbsorberFiniteOrderTower] using
      universalStrongAbsorberTower_unbounded_frame R
  exact selectedAbsorberFiniteOrderTower.exists_proper_growth_after
    hUnbounded N

/-- Unconditionally, there are old-rank movements at arbitrarily
late stages of the ACTUAL selected absorber tower. -/
theorem selectedAbsorberTower_movement_arbitrarily_late
    (N : Nat) :
    ∃ n u : Nat,
      N ≤ n ∧ 3 ≤ u ∧
      u < (universalStrongAbsorberTower n).bound ∧
      universalStrongAbsorberTower_stepMap n u ≠ u := by
  obtain ⟨n,hN,hGrow⟩ :=
    selectedAbsorberTower_exists_properGrowth_after N
  obtain ⟨u,hu3,hu,hMove⟩ :=
    selectedAbsorberTower_properGrowth_moves_old_rank n hGrow
  exact ⟨n,u,hN,hu3,hu,hMove⟩

/-- If the actual tower nevertheless has bounded forward ranks,
then the mandatory motions at future strictly growing stages
must occur beyond every prescribed finite numerical prefix.
This is a NECESSARY finite-injury frontier condition, not a
proof that bounded ranks actually hold. -/
theorem selectedAbsorberTower_lateGrowth_moves_above_cut
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks)
    (r : Nat) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      (universalStrongAbsorberTower n).bound <
        (universalStrongAbsorberTower (n+1)).bound →
      ∃ u : Nat,
        r ≤ u ∧ u < (universalStrongAbsorberTower n).bound ∧
        universalStrongAbsorberTower_stepMap n u ≠ u := by
  have hUnbounded : ∀ t : Nat,
      ∃ n : Nat, t < selectedAbsorberFiniteOrderTower.size n := by
    intro t
    simpa only [selectedAbsorberFiniteOrderTower] using
      universalStrongAbsorberTower_unbounded_frame t
  obtain ⟨N,hFrozen⟩ :=
    selectedAbsorberFiniteOrderTower.exists_eventually_fixed_initial_segments
      hb hUnbounded r
  refine ⟨N,?_⟩
  intro n hn hGrow
  obtain ⟨u,hu3,hu,hMove⟩ :=
    selectedAbsorberTower_properGrowth_moves_old_rank n hGrow
  have hHigh : r ≤ u := by
    by_contra h
    have hLow : u < r := by omega
    have hEq := hFrozen (n-N) u hLow
    have hIndex : N+(n-N) = n := by omega
    rw [hIndex] at hEq
    exact hMove hEq
  exact ⟨u,hHigh,hu,hMove⟩

end DiaryLeafPriority
end ThreeUniformDiaries
