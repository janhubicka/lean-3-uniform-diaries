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

/-- A FINITE palette of literal image profiles on the actual
finite old support S_m suffices to select ONE genuine old
reserved stage f that has compatible arbitrarily late genuine
reserved witnesses at ALL future finite horizons.

Unlike a finite palette of TOTAL functions Nat→Nat, this assumes
only finitely many possibilities for the data that matters:
  p(u) = g(u) for u in countableDiaryFiniteSupport H m.

At each horizon q=m+1+n and target bound M there must be an
ACTUAL q-horizon reserved witness g whose old support profile
lies in the SAME finite W, selected before q,M. Finite diagonal
choice stabilizes one profile p across all q,M; pick f from an
actual witness and restrict it to the old m stage.

NO proof of this finite profile cover W is supplied; in particular
the merged independent q-horizon witness theorem does not give W.
Further, g(m) still varies, so no persistent fixed new-leaf image
or countable diary unavoidability follows. -/
theorem exists_one_old_support_for_all_finite_horizons_of_finite_profile_palette
    {H K : Ordered3Graph Nat}
    (F : Nat → Nat) (m : Nat)
    (W : Finset
      ({u : Nat // u ∈ countableDiaryFiniteSupport H m} → Nat))
    (hCover : ∀ n M : Nat,
      ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        ReservedDiaryStage H K F (m + 1 + n) g ∧
        g m = F t ∧
        (fun u : {u : Nat //
          u ∈ countableDiaryFiniteSupport H m} => g u.val) ∈ W) :
    ∃ f : Nat → Nat,
      PersistentReservedDiaryStage H K F m f ∧
      ∀ n M : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        ReservedDiaryStage H K F (m + 1 + n) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        g m = F t := by
  classical
  let T := {u : Nat // u ∈ countableDiaryFiniteSupport H m}
  let Profile : (Nat → Nat) → T → Nat :=
    fun g u => g u.val
  let P : (T → Nat) → Nat → Nat → Prop := fun p n M =>
    ∃ t : Nat, ∃ g : Nat → Nat,
      M < F t ∧
      ReservedDiaryStage H K F (m + 1 + n) g ∧
      g m = F t ∧
      ∀ u : T, g u.val = p u
  have hDownN : ∀ (p : T → Nat) (n k M : Nat),
      k ≤ n → P p n M → P p k M := by
    intro p n k M hkn
    rintro ⟨t, g, hHigh, Q, hAt, hProfile⟩
    exact ⟨t, g, hHigh, Q.restrict (by omega), hAt, hProfile⟩
  have hDownM : ∀ (p : T → Nat) (n M L : Nat),
      L ≤ M → P p n M → P p n L := by
    intro p n M L hLM
    rintro ⟨t, g, hHigh, Q, hAt, hProfile⟩
    exact ⟨t, g, lt_of_le_of_lt hLM hHigh, Q, hAt, hProfile⟩
  have hFiniteCover : ∀ n M : Nat,
      ∃ p : T → Nat, p ∈ W ∧ P p n M := by
    intro n M
    obtain ⟨t, g, hHigh, Q, hAt, hW⟩ := hCover n M
    have hpW : Profile g ∈ W := by
      simpa only [Profile] using hW
    refine ⟨Profile g, hpW, t, g, hHigh, Q, hAt, ?_⟩
    intro u
    rfl
  obtain ⟨p, hp, hAll⟩ :=
    finite_choice_persistent_of_two_downward_parameters
      W P hDownN hDownM hFiniteCover
  obtain ⟨t₀, g₀, hHigh₀, Q₀, hAt₀, hProfile₀⟩ :=
    hAll 0 0
  have P₀ : ReservedDiaryStage H K F m g₀ :=
    Q₀.restrict (by omega)
  have hAllCompatible : ∀ n M : Nat,
      ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        ReservedDiaryStage H K F (m + 1 + n) g ∧
        CofinalDiaryStageCompatible H m g₀ g ∧
        g m = F t := by
    intro n M
    obtain ⟨t, g, hHigh, Q, hAt, hProfile⟩ := hAll n M
    have hCompatible : CofinalDiaryStageCompatible H m g₀ g := by
      intro x hx
      let u : T := ⟨x, hx⟩
      exact (hProfile u).trans (hProfile₀ u).symm
    exact ⟨t, g, hHigh, Q, hCompatible, hAt⟩
  have hPersistent : PersistentReservedDiaryStage H K F m g₀ := by
    refine ⟨P₀, ?_⟩
    intro n
    obtain ⟨t, g, hHigh, Q, hCompat, hAt⟩ := hAllCompatible n 0
    exact ⟨g, Q.restrict (by omega), hCompat⟩
  exact ⟨g₀, hPersistent, hAllCompatible⟩

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
