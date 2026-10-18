import ThreeUniformDiaries.DiaryFiniteOrderedSumBitCausality
import ThreeUniformDiaries.DiaryFiniteOrderedSumFuturePrefix

/-!
# A well-founded choice of cross-copy Devlin orientations

The finite two-block carrier has an orientation function
Nat → Bool. The correct cross Devlin-1 bit at left leaf u is
the literal LexEarlier comparison with a representative right
leaf in the RESULTING carrier, so there is an apparent
fixed-point requirement.

The preceding causality theorem says that comparison at u
depends ONLY on earlier orientation bits, not on the bit at u
or any later bit. We first formalize a reusable finite
triangular Boolean fixed-point theorem. Apply it directly to
the genuine carrier's LexEarlier predicate. This proves that
a single choice of orientation bits satisfies the required
cross V3-marker-1 equation for ALL right leaves, not just
one representative.

This does NOT yet establish the full ordered-sum RolePrediary:
right/right V3, roles, V1/V2 witness and coherence, and
protected numerical meets are independent obligations.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A causal Boolean functional on a FINITE initial segment has
a fixed point there, even when its output at i depends on all
earlier bits in an arbitrary noncomputable way. The construction
chooses the new bit at stage i, leaving earlier bits unchanged. -/
theorem exists_finite_causal_bool_fixedPoint
    (n : Nat) (eval : (Nat → Bool) → Nat → Bool)
    (hcausal : ∀ f g i, i < n →
      (∀ j, j < i → f j = g j) → eval f i = eval g i) :
    ∃ f : Nat → Bool, ∀ i, i < n → f i = eval f i := by
  classical
  have hRec :
      ∀ k : Nat, k ≤ n →
        ∃ f : Nat → Bool, ∀ i, i < k → f i = eval f i := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun _ => false, ?_⟩
      intro i hi
      omega
    | succ k ih =>
      intro hk
      obtain ⟨f, hf⟩ := ih (by omega)
      let g : Nat → Bool := fun j => if j = k then eval f k else f j
      have hPrefix : ∀ j, j < k → f j = g j := by
        intro j hj
        have hne : j ≠ k := by omega
        simp only [g, if_neg hne]
      refine ⟨g, ?_⟩
      intro i hi
      by_cases hik : i = k
      · subst i
        calc
          g k = eval f k := by simp only [g, if_pos rfl]
          _ = eval g k := hcausal f g k (by omega) hPrefix
      · have hiK : i < k := by omega
        have hEq : g i = f i := by
          simp only [g, if_neg hik]
        have hPreI : ∀ j, j < i → f j = g j := by
          intro j hj
          exact hPrefix j (by omega)
        calc
          g i = f i := hEq
          _ = eval f i := hf i hiK
          _ = eval g i := hcausal f g i (by omega) hPreI
  exact hRec n (le_refl n)

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- Evaluate the literal LexEarlier predicate against the
chosen representative right leaf, using the *actual* raw
ordered-sum carrier. -/
noncomputable def finiteTwoBlockOrientationEval
    (H K : Ordered3Graph Nat) (n m v0 : Nat)
    (bits : Nat → Bool) (u : Nat) : Bool := by
  classical
  exact decide (LexEarlier (finiteTwoBlockCarrier H K n m bits)
    u (rightBlockImage n v0))

theorem finiteTwoBlockOrientationEval_true_iff
    (H K : Ordered3Graph Nat) (n m v0 : Nat)
    (bits : Nat → Bool) (u : Nat) :
    finiteTwoBlockOrientationEval H K n m v0 bits u = true ↔
      LexEarlier (finiteTwoBlockCarrier H K n m bits)
        u (rightBlockImage n v0) := by
  classical
  simp [finiteTwoBlockOrientationEval]

/-- This concrete evaluation is causally dependent only on bits
at levels strictly below u, for all u in the left finite block.
This follows from the verified actual-carrier edge prefix theorem,
not from an abstract assumed callback property. -/
theorem finiteTwoBlockOrientationEval_causal
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hshape : ∀ a b c : Nat, K.edge a b c →
      PermittedDiaryEdge K a b c)
    (v0 : Nat) (hv03 : 3 ≤ v0) (hv0m : v0 < m)
    (hv0Leaf : IsLeaf K v0)
    (f g : Nat → Bool) (u : Nat) (hu : u < n)
    (hBefore : ∀ j, j < u → f j = g j) :
    finiteTwoBlockOrientationEval H K n m v0 f u =
      finiteTwoBlockOrientationEval H K n m v0 g u := by
  classical
  have hLex :=
    finiteTwoBlockCarrier_lex_prefix_independent
      FH FK hshape f g u v0 hu hv03 hv0m hv0Leaf hBefore
  unfold finiteTwoBlockOrientationEval
  exact congrArg (fun p : Prop => decide p) (propext hLex)

/-- The ACTUAL finite ordered-sum carrier admits a Boolean
orientation assignment satisfying the literal V3 comparison
against the fixed representative right leaf simultaneously at
EVERY left level. This is the required well-founded choice
instead of assuming a simultaneous solution exists. -/
theorem exists_finiteTwoBlockOrientation_representative
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hshape : ∀ a b c : Nat, K.edge a b c →
      PermittedDiaryEdge K a b c)
    (v0 : Nat) (hv03 : 3 ≤ v0) (hv0m : v0 < m)
    (hv0Leaf : IsLeaf K v0) :
    ∃ bits : Nat → Bool,
      ∀ u : Nat, u < n →
        ((bits u = true) ↔
          LexEarlier (finiteTwoBlockCarrier H K n m bits)
            u (rightBlockImage n v0)) := by
  classical
  let eval : (Nat → Bool) → Nat → Bool :=
    finiteTwoBlockOrientationEval H K n m v0
  have hCausal : ∀ f g i, i < n →
      (∀ j, j < i → f j = g j) → eval f i = eval g i := by
    intro f g i hi hBefore
    exact finiteTwoBlockOrientationEval_causal
      FH FK hshape v0 hv03 hv0m hv0Leaf f g i hi hBefore
  obtain ⟨bits, hFix⟩ :=
    exists_finite_causal_bool_fixedPoint n eval hCausal
  refine ⟨bits, ?_⟩
  intro u hu
  calc
    bits u = true ↔ eval bits u = true := by rw [hFix u hu]
    _ ↔ LexEarlier (finiteTwoBlockCarrier H K n m bits)
        u (rightBlockImage n v0) :=
      finiteTwoBlockOrientationEval_true_iff H K n m v0 bits u

/-- One orientation assignment now satisfies the ACTUAL cross
V3-marker-1 equation for all pairs (left leaf, right leaf).
No assumption of a priori coherent orientation choices remains. -/
theorem exists_finiteTwoBlockOrientation_cross_V3_one
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hshape : ∀ a b c : Nat, K.edge a b c →
      PermittedDiaryEdge K a b c)
    (v0 : Nat) (hv03 : 3 ≤ v0) (hv0m : v0 < m)
    (hv0Leaf : IsLeaf K v0) :
    ∃ bits : Nat → Bool,
      ∀ u v : Nat, 3 ≤ u → u < n → IsLeaf H u →
        3 ≤ v → v < m → IsLeaf K v →
        ((finiteTwoBlockCarrier H K n m bits).edge
            1 u (rightBlockImage n v) ↔
          LexEarlier (finiteTwoBlockCarrier H K n m bits)
            u (rightBlockImage n v)) := by
  obtain ⟨bits, hRep⟩ :=
    exists_finiteTwoBlockOrientation_representative
      FH FK hshape v0 hv03 hv0m hv0Leaf
  refine ⟨bits, ?_⟩
  intro u v hu3 hun huLeaf hv3 hvm hvLeaf
  exact finiteTwoBlockCarrier_cross_V3_one_of_representative
    FH FK hshape bits u v0 hu3 hun huLeaf
    hv03 hv0m hv0Leaf (hRep u hun)
    v hv3 hvm hvLeaf

end DiaryLeafPriority
end ThreeUniformDiaries
