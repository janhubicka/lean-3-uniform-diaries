import Mathlib

/-!
# Track D: a fixed finite profile does not bound an escaping new-leaf image

Abstract *quantifier* countermodel for the conditional finite-to-countable
fusion gate. It is NOT a model of genuine RoleDiary or ReservedDiaryStage.

A complete finite record indexed by `Fin k` is identically zero across
ALL future source horizons; for each horizon there are arbitrarily
large possible images of an additional, independent coordinate.
All horizon stages are nonempty and their fixed profile is literally
the same. Nonetheless no uniform numerical bound on the escaping
coordinate is seen cofinally often.

This shows that the stabilized finite records in the Track A and
Track D interfaces cannot *by quantifier manipulation alone* yield
the genuine `HasCofinalBoundedNextLeafImages` premise.
Diary-specific geometry is needed to force a bound.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A toy stage with an entire fixed finite image record and a
new distinguished coordinate beyond the source horizon. This is NOT
a genuine diary stage. -/
def FixedProfileEscapingStage (k : Nat)
    (profile : Fin k → Nat) (n image : Nat) : Prop :=
  (∀ i : Fin k, profile i = 0) ∧ n < image

/-- Even fixing the WHOLE finite record once for all stages does
not exclude source-horizon escape of an independent new coordinate.

The bound condition intentionally has the same cofinal quantifiers
as the genuine successor criterion: one B works at arbitrarily
large source horizons, not just at one finite horizon. -/
theorem fixed_profile_stages_nonempty_but_new_image_escapes (k : Nat) :
    (∃ profile : Fin k → Nat,
      ∀ n : Nat, ∃ image : Nat,
        FixedProfileEscapingStage k profile n image) ∧
    (∀ profile : Fin k → Nat,
      ¬ ∃ B : Nat, ∀ N : Nat,
        ∃ n : Nat, N ≤ n ∧
          ∃ image : Nat,
            FixedProfileEscapingStage k profile n image ∧
            image ≤ B) := by
  constructor
  · refine ⟨(fun _ => 0), ?_⟩
    intro n
    refine ⟨n + 1, ?_⟩
    exact ⟨(fun _ => rfl), by omega⟩
  · intro profile
    rintro ⟨B, hBound⟩
    obtain ⟨n, hn, image, hStage, hImage⟩ := hBound B
    have hEscape : n < image := hStage.2
    omega

#print axioms fixed_profile_stages_nonempty_but_new_image_escapes

end DiaryLeafPriority
end ThreeUniformDiaries
