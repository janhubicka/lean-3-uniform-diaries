import ThreeUniformDiaries.DiaryFlipGuidedBranch

/-!
# A finite causal fixed-point lemma for correcting target flips

The published "equivalently" direction of the diary flip
property tries to choose the source flip so that its bits cancel
the bits of an arbitrary flip of the universal target.

For this diagonal choice to exist, the target bit read at the
image of each source split must depend ONLY on earlier source
choices. We formulate this dependency exactly and derive a
fixed point from the already verified guided-branch recursion.

This is a PURELY BOOLEAN theorem. It does not establish that
the geometric embeddings into a proposed target satisfy the
causality hypothesis. The existing 2-split root obstruction
shows that a naive chronological prefix-tree family cannot
provide the necessary coherent embeddings.

The complement map on one bit is also proved fixed-point-free,
showing why mere joint embedding of all source flips gives
NO substitute for the causality condition.
-/

namespace ThreeUniformDiaries
namespace FlipGuidedBranch

/-- Complete a finite prefix of bits by zeros to an arbitrary
ambient length. This is the input used when asking a causal
bit map about its next coordinate. -/
def zeroExtendPrefix (n m : Nat)
    (prefix : Fin m → Bool) : Fin n → Bool :=
  fun j => if hj : j.val < m then prefix ⟨j.val,hj⟩ else false

/-- Strict prefix causality: the value of F at coordinate i
may depend on strictly EARLIER bits, but not on i itself or any
later coordinate. -/
def StrictlyPrefixCausal (n : Nat)
    (F : (Fin n → Bool) → (Fin n → Bool)) : Prop :=
  ∀ (b c : Fin n → Bool) (i : Fin n),
    (∀ j : Fin n, j.val < i.val → b j = c j) →
      F b i = F c i

/-- Read the next bit of an abstract strict-prefix-causal
Boolean map from a finite prefix extended by zero. -/
def causalFeedbackStep (n : Nat)
    (F : (Fin n → Bool) → (Fin n → Bool))
    (m : Nat) (prefix : Fin m → Bool) : Bool :=
  if hm : m < n then
    F (zeroExtendPrefix n m prefix) ⟨m,hm⟩
  else false

/-- A strict-prefix-causal Boolean self-map on finite words
has a fixed point, constructed by genuinely finite-prefix
feedback. No assumption of monotonicity or continuity is used,
apart from the explicit strict prefix dependence. -/
theorem exists_fixedPoint_of_strictlyPrefixCausal
    (n : Nat)
    (F : (Fin n → Bool) → (Fin n → Bool))
    (hCausal : StrictlyPrefixCausal n F) :
    ∃ b : Fin n → Bool, F b = b := by
  let step := causalFeedbackStep n F
  let bits : Nat → Bool := guidedBit step
  let b : Fin n → Bool := fun i => bits i.val
  refine ⟨b,?_⟩
  funext i
  let prefix : Fin i.val → Bool := fun j => bits j.val
  have hPrefix : ∀ j : Fin n, j.val < i.val →
      zeroExtendPrefix n i.val prefix j = b j := by
    intro j hj
    simp only [zeroExtendPrefix, dif_pos hj]
    rfl
  have hCausalAt :
      F (zeroExtendPrefix n i.val prefix) i = F b i :=
    hCausal (zeroExtendPrefix n i.val prefix) b i hPrefix
  have hStep :
      bits i.val = F (zeroExtendPrefix n i.val prefix) i := by
    have heq := guidedBit_step step i.val
    simpa only [step, causalFeedbackStep, dif_pos i.isLt] using heq
  exact hCausalAt.symm.trans hStep.symm

/-- Joint embedding alone does not provide a fixed-point
principle for arbitrary transformations of flip words:
complementing the unique Boolean bit has NO fixed point. -/
theorem complement_oneBit_has_no_fixedPoint :
    ¬ ∃ b : Fin 1 → Bool,
      (fun i : Fin 1 => !b i) = b := by
  rintro ⟨b,h⟩
  have hb := congrFun h (0 : Fin 1)
  cases hbit : b (0 : Fin 1) <;> simp [hbit] at hb

end FlipGuidedBranch
end ThreeUniformDiaries
