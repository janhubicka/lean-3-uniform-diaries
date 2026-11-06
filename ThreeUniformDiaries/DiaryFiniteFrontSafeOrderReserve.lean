import ThreeUniformDiaries.DiaryFiniteFrontCertifiedFusion
import ThreeUniformDiaries.DiaryFutureReserveFusion
import ThreeUniformDiaries.DiaryCofinalStageRestrictions

/-!
# Track B: finitely persistent fronts necessarily reserve every source gap

The existing FiniteCofinalDiaryFronts.Safe predicate selects finite-stage
maps that have compatible genuine admissible extensions at ALL later
finite horizons. The earlier finite-order reserve API requires
  f(x) + (y-x) <= f(y)
for EVERY pair x<y in the old source support.

We prove this numerical reserve is not an extra assumption on the
safe finite-front subsystem. Choose one sufficiently late horizon
whose actual leaf-meet support contains every source vertex in the
interval [x,y]. The stage map at that horizon is strictly increasing
on the WHOLE interval; its accumulated strict inequalities force
at least y-x target steps. Compatibility fixes the old endpoints,
so the same reserve inequality already holds at the old stage.

Consequently each Safe front member is a genuine ReservedDiaryStage.
This is a NECESSARY property of safe fronts, NOT a construction of
nonempty bounded fronts or a proof of relative role-sensitive
extensions. The numerical reserve alone does not force diary V/E/S
types or target flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A finite admissible support map that sees every source integer
from x through y must preserve their full numerical gap. There
is no global strict-monotonicity assumption outside this interval. -/
theorem AdmissibleCofinalDiaryStage.gap_of_complete_interval
    {H K : Ordered3Graph Nat} {F : Nat → Nat}
    {n : Nat} {g : Nat → Nat}
    (Q : AdmissibleCofinalDiaryStage H K F n g)
    (x y : Nat) (hxy : x ≤ y)
    (hInterval : ∀ z : Nat, x ≤ z → z ≤ y →
      z ∈ countableDiaryFiniteSupport H n) :
    g x + (y - x) ≤ g y := by
  have hBound (k : Nat) (hxk : x ≤ k) (hky : k ≤ y) :
      g x + (k - x) ≤ g k := by
    induction k, hxk using Nat.le_induction with
    | base =>
        simp
    | succ k hxk ih =>
        have hk : k ∈ countableDiaryFiniteSupport H n :=
          hInterval k hxk (by omega)
        have hk1 : k + 1 ∈ countableDiaryFiniteSupport H n :=
          hInterval (k+1) (by omega) hky
        have hStep : g k < g (k+1) :=
          Q.ordered k (k+1) hk hk1 (by omega)
        omega
  exact hBound y hxy (le_refl y)

namespace FiniteCofinalDiaryFronts

variable {H K : Ordered3Graph Nat} {DH : RoleDiary H}
variable {F : Nat → Nat}

/-- Every finitely persistent front member has enough TARGET order
room for ALL not-yet-selected source vertices between any two old
supported vertices. This property is inferred from arbitrary finite
horizon compatibility, NOT imposed on the definition of a front. -/
theorem safe_future_order_reserve
    (P : FiniteCofinalDiaryFronts DH K F)
    (m : Nat) (f : Nat → Nat)
    (hf : P.Safe m f) :
    FutureOrderReserve H m f := by
  intro x y hx hy hxy
  obtain ⟨s,hPrefix⟩ :=
    countableDiaryFiniteSupport_contains_finset DH
      (Finset.range (y+1))
  let n : Nat := max m s
  have hmn : m ≤ n := le_max_left m s
  have hsn : s ≤ n := le_max_right m s
  obtain ⟨g,hg,hCompat⟩ := hf.2 n hmn
  have Q : AdmissibleCofinalDiaryStage H K F n g :=
    P.admissible n g hg
  have hInterval : ∀ z : Nat, x ≤ z → z ≤ y →
      z ∈ countableDiaryFiniteSupport H n := by
    intro z hxz hzy
    have hzPrefix : z ∈ Finset.range (y+1) :=
      Finset.mem_range.mpr (by omega)
    exact countableDiaryFiniteSupport_mono H s n hsn
      (hPrefix z hzPrefix)
  have hGap : g x + (y-x) ≤ g y :=
    Q.gap_of_complete_interval x y (Nat.le_of_lt hxy)
      hInterval
  rw [hCompat x hx,hCompat y hy] at hGap
  exact hGap

/-- The entire survivor subsystem of any finite front system
consists of genuine reserved diary stages: it cannot contain
numerically compressed dead-end embeddings. No converse is
asserted, since numerical reserve alone does not realize the
required future split and leaf types. -/
theorem safe_is_reserved
    (P : FiniteCofinalDiaryFronts DH K F)
    (m : Nat) (f : Nat → Nat)
    (hf : P.Safe m f) :
    ReservedDiaryStage H K F m f := by
  exact ⟨P.admissible m f hf.1,
    P.safe_future_order_reserve m f hf⟩

/-- Equivalently, an admissible front stage violating even one
original source gap can never be infinitely persistent.
This is an adversarial rejection test for proposed finite fronts. -/
theorem not_safe_of_compressed_gap
    (P : FiniteCofinalDiaryFronts DH K F)
    (m : Nat) (f : Nat → Nat)
    (x y : Nat)
    (hx : x ∈ countableDiaryFiniteSupport H m)
    (hy : y ∈ countableDiaryFiniteSupport H m)
    (hxy : x < y)
    (hBad : f y < f x + (y-x)) :
    ¬ P.Safe m f := by
  intro hSafe
  have hReserve := P.safe_future_order_reserve m f hSafe
  have hGap := hReserve x y hx hy hxy
  omega

end FiniteCofinalDiaryFronts
end DiaryLeafPriority
end ThreeUniformDiaries
