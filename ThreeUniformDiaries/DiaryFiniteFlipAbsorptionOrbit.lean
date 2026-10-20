import ThreeUniformDiaries.DiaryFiniteFlipTransitivity

/-!
# Absorption is an invariant of the target flip class

The finite diary flip relation is now verified reflexive, symmetric,
and transitive. This makes the second flip-property target condition
well behaved: whether EVERY target flip admits a protected copy of
the original source cannot depend on which representative diary
in the same finite target flip class was initially chosen.

This theorem is a genuine mathematical equivalence of the
absorption *predicate*, NOT a proof that the predicate holds.
It avoids the false inference that a source flip must be the
unflipped source; the original source A stays fixed throughout.

The historical absorption predicate does not itself enforce the
finite target image bound. A bound-corrected version is being
audited separately, so this module does not strengthen that claim.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A B C : Ordered3Graph Nat} {n k : Nat}

/-- Every-target-flip absorption is invariant under changing
the target diary to another genuine finite flip of that target.
The source is not changed. -/
theorem absorbsEveryTargetFlip_target_flip_iff
    (F : FiniteDiaryFlip B C k) :
    AbsorbsEveryTargetFlip A B n k ↔
      AbsorbsEveryTargetFlip A C n k := by
  constructor
  · intro h D hCD
    exact h D (F.trans hCD)
  · intro h D hBD
    exact h D (F.symm.trans hBD)

/-- Any every-target-flip absorption proof must in particular
give a protected copy of the fixed unflipped source inside
the original target (using reflexivity of the flip relation).
This is only a necessary condition. -/
theorem absorbsEveryTargetFlip_self_copy
    (DB : FiniteRoleDiaryBlock B k)
    (h : AbsorbsEveryTargetFlip A B n k) :
    ∃ f : Nat → Nat, FiniteMeetEmbedding A B n f := by
  exact h B (FiniteDiaryFlip.refl DB)

end DiaryLeafPriority
end ThreeUniformDiaries
