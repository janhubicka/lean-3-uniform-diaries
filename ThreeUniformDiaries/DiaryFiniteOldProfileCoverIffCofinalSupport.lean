import ThreeUniformDiaries.DiaryTwoParameterFiniteOldSupportChoice

/-!
# Track A audit: finite old-profile horizon cover IFF one common cofinal old support

English-first adversarial audit: 3-uniform-diaries PR #356.

The positive merged Track A finite-support-profile diagonal theorem
#1495 constructs ONE actual finitely persistent old support f
from a finite palette W of literal S_m image profiles recurring
at every source future horizon and target numerical cutoff.

The converse is elementary but CRUCIAL for the audit:
if ONE such f already exists, the singleton palette consisting
of the literal restriction f|S_m satisfies the finite cover.

Thus the finite-palette hypothesis and the all-horizon common-f
conclusion are EQUIVALENT existence assertions on the SAME fixed
target leaf range F. Merely phrasing the open task using a finite
W does NOT solve it. A geometric construction of the actual W
is still essential, and the merged all-horizon generic support
drift no-go forbids uniform W over all arbitrary unordered
generic refinements when two earlier source leaves are selected.

Neither condition fixes the new image g(m) throughout later
horizons or implies countable diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- On one FIXED prescribed target leaf range F, one FINITE
set of literal supported old-image profiles covers actual
reserved stages with cofinally high new-leaf images for
EVERY finite future source horizon.

W is existential but is chosen before BOTH horizon n and
target bound M. No old stage f is part of the definition. -/
def HasFiniteOldProfileCoverAtAllHorizons
    (H K : Ordered3Graph Nat) (F : Nat → Nat)
    (m : Nat) : Prop :=
  ∃ W : Finset
      ({u : Nat // u ∈ countableDiaryFiniteSupport H m} → Nat),
    ∀ n M : Nat,
      ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        ReservedDiaryStage H K F (m + 1 + n) g ∧
        g m = F t ∧
        (fun u : {u : Nat //
          u ∈ countableDiaryFiniteSupport H m} =>
          g u.val) ∈ W

/-- One ACTUAL finitely persistent reserved old stage f
admits genuine compatible q-horizon stages with cofinally
high new-leaf images at EVERY later finite horizon q.
All old support images are fixed literally but different
q-horizon witnesses can map the new leaf to different values. -/
def HasOneFixedOldSupportCofinalAtAllHorizons
    (H K : Ordered3Graph Nat) (F : Nat → Nat)
    (m : Nat) : Prop :=
  ∃ f : Nat → Nat,
    PersistentReservedDiaryStage H K F m f ∧
    ∀ n M : Nat,
      ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        ReservedDiaryStage H K F (m + 1 + n) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        g m = F t

/-- Exact iff: finite profile palette existence on a fixed
range F is just another presentation of the hard common-old-
support / cofinal all-horizon recurrence existence assertion.

Forward uses the checked two-parameter finite palette diagonal.
Reverse takes the SINGLETON palette of f restricted to S_m.
This equivalence does not establish either side in arbitrary
prescribed generic leaf ranges. -/
theorem finite_old_profile_cover_iff_one_fixed_cofinal_old_support
    (H K : Ordered3Graph Nat) (F : Nat → Nat)
    (m : Nat) :
    HasFiniteOldProfileCoverAtAllHorizons H K F m ↔
      HasOneFixedOldSupportCofinalAtAllHorizons H K F m := by
  classical
  constructor
  · rintro ⟨W, hCover⟩
    exact exists_one_old_support_for_all_finite_horizons_of_finite_profile_palette
      F m W hCover
  · rintro ⟨f, hPersistent, hAll⟩
    let T := {u : Nat // u ∈ countableDiaryFiniteSupport H m}
    let p : T → Nat := fun u => f u.val
    refine ⟨{p}, ?_⟩
    intro n M
    obtain ⟨t, g, hHigh, Q, hOld, hAt⟩ := hAll n M
    refine ⟨t, g, hHigh, Q, hAt, ?_⟩
    have hEq : (fun u : T => g u.val) = p := by
      funext u
      exact hOld u.val u.property
    exact Finset.mem_singleton.mpr hEq

end DiaryLeafPriority
end ThreeUniformDiaries
