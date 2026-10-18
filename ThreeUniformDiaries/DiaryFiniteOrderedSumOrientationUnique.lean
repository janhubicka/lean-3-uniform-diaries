import ThreeUniformDiaries.DiaryFiniteOrderedSumOrientationChoice

/-!
# Uniqueness of the finite causal cross-marker orientation

An arbitrary causal Boolean functional has at most one fixed point
on its finite dependency segment: if two candidate solutions agree
at all preceding indices, their next evaluations agree.

The cross-block Devlin-1 orientation functional was proved causal
in DiaryFiniteOrderedSumOrientationChoice. Thus ANY two choices
satisfying its literal representative V3 equations agree on all
left-block indices, even if they differ beyond that block.
This uniqueness will matter when extending finite ordered sums
to additional blocks without changing earlier marker decisions.

This is NOT an existence theorem for a full pre-diary or an
EVERY-FLIP-of-target absorption argument.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A finite triangular Boolean fixed point is unique on the
finite initial dependency segment. No computability or order
assumptions beyond causality are needed. -/
theorem finite_causal_bool_fixedPoint_agree
    (n : Nat) (eval : (Nat → Bool) → Nat → Bool)
    (hcausal : ∀ f g i, i < n →
      (∀ j, j < i → f j = g j) → eval f i = eval g i)
    (f g : Nat → Bool)
    (hf : ∀ i, i < n → f i = eval f i)
    (hg : ∀ i, i < n → g i = eval g i) :
    ∀ i, i < n → f i = g i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    have hBefore : ∀ j, j < i → f j = g j := by
      intro j hj
      exact ih j hj (by omega)
    calc
      f i = eval f i := hf i hi
      _ = eval g i := hcausal f g i hi hBefore
      _ = g i := (hg i hi).symm

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- A Boolean value is determined by its true/false equality
test, allowing logical V3 equations to become actual fixed-point
equations. -/
theorem bool_eq_of_true_iff
    (b c : Bool) (h : (b = true) ↔ (c = true)) : b = c := by
  cases b <;> cases c <;> simp_all

/-- Two orientation assignments which both satisfy the genuine
representative-right-leaf Devlin-1 equation must agree at every
left level. This uses only the right edge-shape assumption and
causality of the actual ordered-sum carrier. -/
theorem finiteTwoBlockOrientation_representative_unique
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hshape : ∀ a b c : Nat, K.edge a b c →
      PermittedDiaryEdge K a b c)
    (v0 : Nat) (hv03 : 3 ≤ v0) (hv0m : v0 < m)
    (hv0Leaf : IsLeaf K v0)
    (f g : Nat → Bool)
    (hf : ∀ i, i < n →
      ((f i = true) ↔
        LexEarlier (finiteTwoBlockCarrier H K n m f)
          i (rightBlockImage n v0)))
    (hg : ∀ i, i < n →
      ((g i = true) ↔
        LexEarlier (finiteTwoBlockCarrier H K n m g)
          i (rightBlockImage n v0))) :
    ∀ i, i < n → f i = g i := by
  let eval := finiteTwoBlockOrientationEval H K n m v0
  have hcausal : ∀ f g i, i < n →
      (∀ j, j < i → f j = g j) → eval f i = eval g i := by
    intro a b i hi hbefore
    exact finiteTwoBlockOrientationEval_causal
      FH FK hshape v0 hv03 hv0m hv0Leaf a b i hi hbefore
  have hfFix : ∀ i, i < n → f i = eval f i := by
    intro i hi
    have hBit : (f i = true) ↔ (eval f i = true) :=
      (hf i hi).trans
        (finiteTwoBlockOrientationEval_true_iff
          H K n m v0 f i).symm
    exact bool_eq_of_true_iff (f i) (eval f i) hBit
  have hgFix : ∀ i, i < n → g i = eval g i := by
    intro i hi
    have hBit : (g i = true) ↔ (eval g i = true) :=
      (hg i hi).trans
        (finiteTwoBlockOrientationEval_true_iff
          H K n m v0 g i).symm
    exact bool_eq_of_true_iff (g i) (eval g i) hBit
  exact finite_causal_bool_fixedPoint_agree n eval hcausal
    f g hfFix hgFix

end DiaryLeafPriority
end ThreeUniformDiaries
