import ThreeUniformDiaries.DiaryFixedProfileUniformBoundCriterion

/-!
# Adversarial counterexample: same tail-cone replacement does not imply persistence

Track D has now verified a genuine geometric theorem: once an immediate
reserved successor sends its new source leaf to v, the image can be
replaced by any sufficiently late leaf in the SAME full singleton-type
cone, keeping the old and new nonleaf support unchanged.

The tempting compactness inference is INVALID even abstractly:
  * every finite horizon is realizable;
  * each horizon's set of valid leaf values is upward-closed;
  * every such set contains arbitrarily late values;
  * all these values may have the SAME fixed finite split profile;
yet no fixed leaf value need persist at every finite horizon.

This module supplies an exact finite-horizon countermodel: an image v
works at horizon n precisely when n <= v. It is deliberately NOT a
counterexample inside an actual full role diary. Rather, it blocks an
unjustified inference from tail-cone replacement to countable diary
unavoidability. To exclude this obstruction in the actual diary class,
one still needs an independent bounded/persistent choice theorem or
new geometric tail-richness invariant.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- An abstract finite-horizon viability predicate, with one fixed
(nonleaf) profile and every sufficiently late leaf viable at horizon n.
Here n is the finite continuation horizon, v the chosen leaf image. -/
def tailConeEscapingHorizon (v n : Nat) : Prop :=
  n ≤ v

/-- Every finite continuation horizon admits at least one candidate.
There is no prescribed bound on the candidate image. -/
theorem tailConeEscapingHorizon_nonempty_each_horizon :
    ∀ n : Nat, ∃ v : Nat, tailConeEscapingHorizon v n := by
  intro n
  exact ⟨n, Nat.le_refl n⟩

/-- Compatibility is monotone under restriction to any earlier horizon. -/
theorem tailConeEscapingHorizon_downward
    (v n k : Nat) (hkn : k ≤ n)
    (h : tailConeEscapingHorizon v n) :
    tailConeEscapingHorizon v k := by
  dsimp [tailConeEscapingHorizon] at *
  omega

/-- STRONG tail replacement: if v is a valid candidate at horizon n,
then ANY later leaf image w >= v is also valid at the SAME horizon. -/
theorem tailConeEscapingHorizon_upward
    (n v w : Nat) (hvw : v ≤ w)
    (h : tailConeEscapingHorizon v n) :
    tailConeEscapingHorizon w n := by
  dsimp [tailConeEscapingHorizon] at *
  omega

/-- Each finite horizon admits arbitrarily late candidate leaves,
with no change in the (trivial) finite split/type profile. -/
theorem tailConeEscapingHorizon_arbitrarily_late
    (n B : Nat) :
    ∃ v : Nat, B < v ∧ tailConeEscapingHorizon v n := by
  refine ⟨B + n + 1, by omega, ?_⟩
  change n ≤ B + n + 1
  omega

/-- Every fixed candidate eventually fails at a later finite horizon. -/
theorem tailConeEscapingHorizon_each_candidate_dies
    (v : Nat) :
    ∃ n : Nat, ¬ tailConeEscapingHorizon v n := by
  refine ⟨v + 1, ?_⟩
  simp only [tailConeEscapingHorizon]
  omega

/-- Despite all the above finite and tail-abundance properties,
NO ONE fixed leaf image can handle every finite horizon. -/
theorem tailConeEscapingHorizon_no_persistent_image :
    ¬ ∃ v : Nat, ∀ n : Nat, tailConeEscapingHorizon v n := by
  rintro ⟨v, hv⟩
  exact (tailConeEscapingHorizon_each_candidate_dies v).elim
    (fun n hn => hn (hv n))

/-- Nor can one bound the choice of viable leaf image UNIFORMLY
across every finite horizon; this is exactly the missing boundedness
hypothesis in the checked Track C/D persistence criterion. -/
theorem tailConeEscapingHorizon_no_uniform_image_bound :
    ¬ ∃ B : Nat, ∀ n : Nat,
      ∃ v : Nat, tailConeEscapingHorizon v n ∧ v ≤ B := by
  rintro ⟨B, hBound⟩
  obtain ⟨v, hv, hUpper⟩ := hBound (B + 1)
  dsimp [tailConeEscapingHorizon] at hv
  omega

/-- Formal adversarial refutation of the INVALID abstract principle:
downward horizon compatibility, upward tail replacement, and finite
horizon nonemptiness do not by themselves give a persistent image.

This quantifier-level regression prevents the conditional tail-cone
replacement theorem from being misused as the still-open countable
diary-unavoidability theorem. -/
theorem upwardClosedHorizonCompactness_false :
    ¬ (∀ R : Nat → Nat → Prop,
      (∀ v n k : Nat, k ≤ n → R v n → R v k) →
      (∀ n v w : Nat, v ≤ w → R v n → R w n) →
      (∀ n : Nat, ∃ v : Nat, R v n) →
      ∃ v : Nat, ∀ n : Nat, R v n) := by
  intro hFalse
  obtain ⟨v, hv⟩ := hFalse tailConeEscapingHorizon
    tailConeEscapingHorizon_downward
    tailConeEscapingHorizon_upward
    tailConeEscapingHorizon_nonempty_each_horizon
  exact tailConeEscapingHorizon_no_persistent_image ⟨v, hv⟩

end DiaryLeafPriority
end ThreeUniformDiaries
