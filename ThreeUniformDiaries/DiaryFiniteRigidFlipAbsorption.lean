import ThreeUniformDiaries.DiaryFiniteBoundedUniversality
import ThreeUniformDiaries.DiaryFinitePullbackProtectedEmbedding

/-!
# Unconditional every-target-flip absorption for flip-rigid sources

The general second flip property remains unresolved. A useful
boundary case is already implied by the verified finite universal
target and the canonical geometric source pullback.

Suppose A is flip-rigid: every genuine finite diary flip of A on
its prescribed vertex interval is literally A itself. Then for
any target flip B' of a finite universal diary B containing A,
the pullback of B' along a fixed bounded protected copy of A in B
is a genuine source flip P of A. Rigidity makes P=A, and the
verified full mixed-meet pullback embedding gives A->B'.

This proves the STRONG bounded every-target-flip absorption
property, not only the first joint-embedding direction, for every
source with a singleton real flip orbit. There is no independent
Boolean control assumption and no use of the impossible raw-code
feedback injectivity premise.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A finite source diary is flip-rigid when every genuine finite
identity-preembedding flip is the SAME finite edge table. -/
def FiniteDiaryFlipRigid
    (A : Ordered3Graph Nat) (n : Nat) : Prop :=
  ∀ P : Ordered3Graph Nat, FiniteDiaryFlip A P n → P = A

/-- For a flip-rigid source, any chosen bounded protected copy
inside B survives in EVERY genuine target flip of B. -/
theorem boundedEmbedding_survives_every_target_flip_of_rigid
    {A B : Ordered3Graph Nat} {n k : Nat} {f : Nat → Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (E : FiniteBoundedMeetEmbedding A B n k f)
    (hRigid : FiniteDiaryFlipRigid A n) :
    ∀ B' : Ordered3Graph Nat,
      ∀ F : FiniteDiaryFlip B B' k,
        FiniteBoundedMeetEmbedding A B' n k f := by
  intro B' F
  let P := finiteDiaryPullbackGraph B' n f
  have FP : FiniteDiaryFlip A P n :=
    finiteDiaryPullbackGraph_is_sourceFlip
      DA E.toMeetEmbedding E.image_bound F
  have hEq : P = A := hRigid P FP
  have EP : FiniteBoundedMeetEmbedding P B' n k f :=
    finiteDiaryPullbackGraph_boundedEmbedding_into_targetFlip
      DA E F
  simpa only [hEq] using EP

/-- The strong SECOND flip property holds unconditionally for
EVERY flip-rigid source: there is a GENUINE finite target diary
such that the original source appears by a bounded fully
mixed-meet preserving embedding in EVERY finite target flip. -/
theorem exists_finite_absorbing_target_of_flip_rigid
    (A : Ordered3Graph Nat) (n : Nat)
    (DA : FiniteRoleDiaryBlock A n)
    (hRigid : FiniteDiaryFlipRigid A n) :
    ∃ (B : Ordered3Graph Nat) (k : Nat),
      FiniteRoleDiaryBlock B k ∧
      AbsorbsEveryTargetFlipInside A B n k := by
  obtain ⟨B,k,DB,hUniversal⟩ :=
    exists_finiteDiary_for_all_source_flips_bounded A n DA
  obtain ⟨f,E⟩ :=
    hUniversal A (FiniteDiaryFlip.refl DA)
  refine ⟨B,k,DB,?_⟩
  intro B' F
  exact ⟨f,boundedEmbedding_survives_every_target_flip_of_rigid
    DA E hRigid B' F⟩

end DiaryLeafPriority
end ThreeUniformDiaries
