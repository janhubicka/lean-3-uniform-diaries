import ThreeUniformDiaries.DiaryFullNewGeneratorProfileStabilisation
import ThreeUniformDiaries.DiaryFixedOldSupportCofinalFiniteHorizon

/-!
# Track A/D: a FINITE palette fixes ONE complete old support across ALL horizons

English-first adversarial audit: 3-uniform-diaries PR #348.

Track D #1489 proves that for EACH future source horizon there
is SOME complete old support with cofinally high actual reserved
new-leaf images, but the chosen old support may drift with the
horizon. It does not prove existence of a common finite palette
of possible old support records across ALL source horizons.

The general finite-choice lemma below uses only the previously
checked one-parameter finite-choice theorem, applied to the
diagonal P(v,n,n). Downward closure along BOTH horizon and
target-value-bound coordinates then yields ONE record v valid
for every pair (n,M).

In the actual reserved-stage corollary, horizon downward closure
comes from the checked genuine ReservedDiaryStage.restrict,
and numerical-bound downward closure comes from M < F(t).

The corollary assumes an independently supplied FINITE old-map
palette W that covers all horizons. This is NOT provided by #1489.
Even its conclusion leaves the NEW leaf image g(m) varying with
horizon, so it does not give persistent finite-image covers or
the full countable diary unavoidability theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A two-parameter finite choice principle for downward predicates.

If a common finite palette W contains at least one witness for
every pair of natural parameters (n,M), and P is downward closed
in each of the two parameters, then ONE palette member works for
every (n,M). The proof applies the already verified one-parameter
finite choice lemma to the diagonal P(v,k,k), then takes
k=max(n,M). No infinite compactness assumption occurs. -/
theorem finite_choice_persistent_of_two_downward_parameters
    {α : Type*} [DecidableEq α]
    (W : Finset α) (P : α → Nat → Nat → Prop)
    (hDownN : ∀ (v : α) (n k M : Nat),
      k ≤ n → P v n M → P v k M)
    (hDownM : ∀ (v : α) (n M L : Nat),
      L ≤ M → P v n M → P v n L)
    (hCover : ∀ n M : Nat, ∃ v : α, v ∈ W ∧ P v n M) :
    ∃ v : α, v ∈ W ∧ ∀ n M : Nat, P v n M := by
  classical
  let Q : α → Nat → Prop := fun v k => P v k k
  have hQDown : ∀ (v : α) (n k : Nat),
      k ≤ n → Q v n → Q v k := by
    intro v n k hkn h
    exact hDownM v k n k hkn
      (hDownN v n k n hkn h)
  have hQCover : ∀ k : Nat,
      ∃ v : α, v ∈ W ∧ Q v k := by
    intro k
    exact hCover k k
  obtain ⟨v, hv, hAll⟩ :=
    finite_choice_persistent_of_downward_type
      W Q hQDown hQCover
  refine ⟨v, hv, ?_⟩
  intro n M
  let k := max n M
  exact hDownM v n k M (le_max_right n M)
    (hDownN v k n k (le_max_left n M) (hAll k))

/-- The actual old reserved stage support can be chosen UNIFORMLY
across ALL later finite source horizons if its admissible values
lie in one fixed FINITE palette W of total old maps.

At every source horizon n, one palette map f_n must support
genuinely reserved (m+1+n)-horizon witnesses with arbitrarily
large new image. The theorem stabilizes one f for all n and M.
It does not stabilize g(m): its witness still varies with n,M.
No old-map palette is produced here. -/
theorem exists_one_old_support_for_all_finite_horizons_of_finite_palette
    {H K : Ordered3Graph Nat}
    (F : Nat → Nat) (m : Nat)
    (W : Finset (Nat → Nat))
    (hEachHorizon : ∀ n : Nat,
      ∃ f : Nat → Nat,
        f ∈ W ∧
        ReservedDiaryStage H K F m f ∧
        ∀ M : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
          M < F t ∧
          ReservedDiaryStage H K F (m + 1 + n) g ∧
          CofinalDiaryStageCompatible H m f g ∧
          g m = F t) :
    ∃ f : Nat → Nat,
      f ∈ W ∧
      ReservedDiaryStage H K F m f ∧
      ∀ n M : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        ReservedDiaryStage H K F (m + 1 + n) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        g m = F t := by
  classical
  let P : (Nat → Nat) → Nat → Nat → Prop := fun f n M =>
    ReservedDiaryStage H K F m f ∧
      ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        ReservedDiaryStage H K F (m + 1 + n) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        g m = F t
  have hDownN : ∀ (f : Nat → Nat) (n k M : Nat),
      k ≤ n → P f n M → P f k M := by
    intro f n k M hkn h
    obtain ⟨Pf, t, g, hHigh, Q, hOld, hAt⟩ := h
    exact ⟨Pf, t, g, hHigh, Q.restrict (by omega), hOld, hAt⟩
  have hDownM : ∀ (f : Nat → Nat) (n M L : Nat),
      L ≤ M → P f n M → P f n L := by
    intro f n M L hLM h
    obtain ⟨Pf, t, g, hHigh, Q, hOld, hAt⟩ := h
    exact ⟨Pf, t, g, lt_of_le_of_lt hLM hHigh, Q, hOld, hAt⟩
  have hCover : ∀ n M : Nat,
      ∃ f : Nat → Nat, f ∈ W ∧ P f n M := by
    intro n M
    obtain ⟨f, hf, Pf, hAll⟩ := hEachHorizon n
    obtain ⟨t, g, hHigh, Q, hOld, hAt⟩ := hAll M
    exact ⟨f, hf, Pf, t, g, hHigh, Q, hOld, hAt⟩
  obtain ⟨f, hf, hAll⟩ :=
    finite_choice_persistent_of_two_downward_parameters
      W P hDownN hDownM hCover
  refine ⟨f, hf, (hAll 0 0).1, ?_⟩
  intro n M
  exact (hAll n M).2

/-- The finite palette hypothesis above CANNOT be simply omitted:
for the infinite palette of all natural-number profile values,
each (n,M) has a common upper bound f, but no ONE finite f
bounds every n and M. This is a quantifier counterexample,
NOT a counterexample to diary unavoidability. -/
theorem infinite_palette_cannot_be_diagonally_stabilized :
    (∀ n M : Nat, ∃ f : Nat, n ≤ f ∧ M ≤ f) ∧
    ¬ (∃ f : Nat, ∀ n M : Nat, n ≤ f ∧ M ≤ f) := by
  constructor
  · intro n M
    exact ⟨max n M, le_max_left n M, le_max_right n M⟩
  · rintro ⟨f, hf⟩
    have h := (hf (f + 1) 0).1
    omega

end DiaryLeafPriority
end ThreeUniformDiaries
