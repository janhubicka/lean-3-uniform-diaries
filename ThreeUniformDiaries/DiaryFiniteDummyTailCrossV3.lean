import ThreeUniformDiaries.DiaryFiniteDummyTailOldMeets
import ThreeUniformDiaries.DiaryLexFutureLeafLocality
import ThreeUniformDiaries.DiaryLexPrefixEdgeInvariance
import ThreeUniformDiaries.DiaryFiniteOrderedSumOrientationChoice

/-!
# Causal finite-to-infinite dummy-tail Devlin marker choice

Every dummy leaf z>=n has the same singleton test column below
the original finite block. Such a column contains only Devlin
marker tests (1,u,z)/(2,u,z) for original leaves u<n, with bits
chosen uniformly in z.

The literal LexEarlier comparison of old u<n against a dummy
tail leaf z is therefore independent of WHICH dummy leaf z is
used. Moreover, its value depends only on bits at earlier old
levels t<u: the column ending at u is induced from the source,
and the dummy column restricted to t<u reads only earlier bits.

Apply the already validated finite triangular Boolean fixed-point
theorem to the ACTUAL countable tail carrier and its first dummy
leaf n. The resulting single bit assignment satisfies BOTH
finite-to-tail Devlin V3 markers for every old leaf and EVERY
dummy tail leaf.

This is only the finite-to-tail V3 component. Internal old V3,
tail-to-tail V3 and the remaining global V/E clauses are verified
separately before claiming a countable RolePrediary.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat} {n : Nat}

/-- Before the original finite boundary, every new tail
column has exactly the prescribed cross-marker test profile,
independent of the later dummy endpoint. -/
theorem finiteDummyTailCarrier_tail_column_iff
    (bits : Nat → Bool)
    (a b z : Nat) (hbn : b < n) (hzn : n ≤ z) :
    (finiteDummyTailCarrier H n bits).edge a b z ↔
      (3 ≤ b ∧ IsLeaf H b ∧
        ((a = 1 ∧ bits b = true) ∨
         (a = 2 ∧ bits b = false))) := by
  constructor
  · intro he
    rcases he with hOld | hCross | hTail
    · omega
    · obtain ⟨u,hu3,hun,huLeaf,_hz,hy,hBit⟩ := hCross
      have hEq : u = b := hy.symm
      subst u
      exact ⟨hu3,huLeaf,hBit⟩
    · omega
  · rintro ⟨hb3,hbLeaf,hBit⟩
    exact Or.inr (Or.inl
      ⟨b,hb3,hbn,hbLeaf,hzn,rfl,hBit⟩)

/-- Any two dummy tail vertices have identical singleton
types below ANY cut inside the preceding finite block. -/
theorem finiteDummyTailCarrier_tails_sameOneType_below_frame
    (bits : Nat → Bool)
    (l y z : Nat) (hl : l ≤ n) (hy : n ≤ y) (hz : n ≤ z) :
    (finiteDummyTailCarrier H n bits).SameOneTypeBelow l y z := by
  intro a b hab hb
  have hbn : b < n := by omega
  exact (finiteDummyTailCarrier_tail_column_iff
    bits a b y hbn hy).trans
      (finiteDummyTailCarrier_tail_column_iff
        bits a b z hbn hz).symm

/-- An old vertex's literal LexEarlier orientation to the
entire infinite tail is uniform for ANY chosen marker bits. -/
theorem finiteDummyTailCarrier_lex_uniform_tail
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (u y z : Nat) (hun : u < n)
    (hy : n ≤ y) (hz : n ≤ z) :
    LexEarlier (finiteDummyTailCarrier H n bits) u y ↔
      LexEarlier (finiteDummyTailCarrier H n bits) u z := by
  have huy : u < y := by omega
  have huz : u < z := by omega
  exact lexEarlier_right_congr_of_sameOneTypeBelow
    (finiteDummyTailCarrier H n bits) u y z huy huz
    (finiteDummyTailCarrier_tails_sameOneType_below_frame
      bits u y z (by omega) hy hz)

/-- Under two marker assignments that agree strictly before
old vertex u, the dummy endpoint column below u is identical. -/
theorem finiteDummyTailCarrier_tail_column_prefix_congr
    (f g : Nat → Bool)
    (u z : Nat) (hun : u < n) (hz : n ≤ z)
    (hBefore : ∀ t : Nat, t < u → f t = g t) :
    ∀ a b : Nat, a < b → b < u →
      ((finiteDummyTailCarrier H n f).edge a b z ↔
       (finiteDummyTailCarrier H n g).edge a b z) := by
  intro a b hab hb
  have hbn : b < n := by omega
  calc
    (finiteDummyTailCarrier H n f).edge a b z ↔
      (3 ≤ b ∧ IsLeaf H b ∧
        ((a = 1 ∧ f b = true) ∨
         (a = 2 ∧ f b = false))) :=
      finiteDummyTailCarrier_tail_column_iff f a b z hbn hz
    _ ↔ (3 ≤ b ∧ IsLeaf H b ∧
        ((a = 1 ∧ g b = true) ∨
         (a = 2 ∧ g b = false))) := by
      rw [hBefore b hb]
    _ ↔ (finiteDummyTailCarrier H n g).edge a b z :=
      (finiteDummyTailCarrier_tail_column_iff g a b z hbn hz).symm

/-- The genuine finite-to-tail lex comparison at u does NOT
depend on its own Boolean bit or any later finite bits. -/
theorem finiteDummyTailCarrier_lex_prefix_independent
    (FH : FiniteDiaryEdgeFrame H n)
    (f g : Nat → Bool)
    (u z : Nat) (hun : u < n) (hz : n ≤ z)
    (hBefore : ∀ t : Nat, t < u → f t = g t) :
    (LexEarlier (finiteDummyTailCarrier H n f) u z ↔
      LexEarlier (finiteDummyTailCarrier H n g) u z) := by
  have huz : u < z := by omega
  have hOld : ∀ a b : Nat, a < b → b < u →
      ((finiteDummyTailCarrier H n f).edge a b u ↔
       (finiteDummyTailCarrier H n g).edge a b u) := by
    intro a b hab hb
    calc
      (finiteDummyTailCarrier H n f).edge a b u ↔ H.edge a b u :=
        finiteDummyTailCarrier_finite_edge_iff FH f a b u hun
      _ ↔ (finiteDummyTailCarrier H n g).edge a b u :=
        (finiteDummyTailCarrier_finite_edge_iff FH g a b u hun).symm
  have hTail := finiteDummyTailCarrier_tail_column_prefix_congr
    (H := H) (n := n) f g u z hun hz hBefore
  exact lexEarlier_prefix_congr_of_edge_columns
    (H := finiteDummyTailCarrier H n f)
    (K := finiteDummyTailCarrier H n g)
    u z huz hOld hTail

/-- Evaluate the actual LexEarlier comparison to the FIRST
dummy tail vertex using the current Boolean assignment. -/
noncomputable def finiteDummyTailOrientationEval
    (H : Ordered3Graph Nat) (n : Nat)
    (bits : Nat → Bool) (u : Nat) : Bool := by
  classical
  exact decide (LexEarlier (finiteDummyTailCarrier H n bits) u n)

theorem finiteDummyTailOrientationEval_true_iff
    (H : Ordered3Graph Nat) (n : Nat)
    (bits : Nat → Bool) (u : Nat) :
    finiteDummyTailOrientationEval H n bits u = true ↔
      LexEarlier (finiteDummyTailCarrier H n bits) u n := by
  simp [finiteDummyTailOrientationEval]

/-- True finite-step causality for the actual tail carrier. -/
theorem finiteDummyTailOrientationEval_causal
    (FH : FiniteDiaryEdgeFrame H n)
    (f g : Nat → Bool) (u : Nat) (hun : u < n)
    (hBefore : ∀ t : Nat, t < u → f t = g t) :
    finiteDummyTailOrientationEval H n f u =
      finiteDummyTailOrientationEval H n g u := by
  classical
  have hLex := finiteDummyTailCarrier_lex_prefix_independent
    FH f g u n hun (le_refl n) hBefore
  unfold finiteDummyTailOrientationEval
  exact congrArg (fun p : Prop => decide p) (propext hLex)

/-- A single Boolean sequence satisfies its own actual
finite-to-first-tail LexEarlier equations simultaneously. -/
theorem exists_finiteDummyTailOrientation_fixedPoint
    (FH : FiniteDiaryEdgeFrame H n) :
    ∃ bits : Nat → Bool,
      ∀ u : Nat, u < n →
        (bits u = true ↔
          LexEarlier (finiteDummyTailCarrier H n bits) u n) := by
  classical
  let eval : (Nat → Bool) → Nat → Bool :=
    finiteDummyTailOrientationEval H n
  have hCausal : ∀ f g i, i < n →
      (∀ j, j < i → f j = g j) → eval f i = eval g i := by
    intro f g i hi hBefore
    exact finiteDummyTailOrientationEval_causal
      FH f g i hi hBefore
  obtain ⟨bits, hFix⟩ :=
    exists_finite_causal_bool_fixedPoint n eval hCausal
  refine ⟨bits, ?_⟩
  intro u hu
  calc
    bits u = true ↔ eval bits u = true := by rw [hFix u hu]
    _ ↔ LexEarlier (finiteDummyTailCarrier H n bits) u n :=
      finiteDummyTailOrientationEval_true_iff H n bits u

/-- CHOSEN ACTUAL CROSS V3: for EVERY original finite leaf and
EVERY later dummy tail leaf, BOTH complementary Devlin markers
obey the manuscript's literal mixed-meet LexEarlier predicate. -/
theorem exists_finiteDummyTailOrientation_cross_V3_both
    (FH : FiniteDiaryEdgeFrame H n) :
    ∃ bits : Nat → Bool,
      ∀ u z : Nat, 3 ≤ u → u < n → IsLeaf H u → n ≤ z →
        (((finiteDummyTailCarrier H n bits).edge 1 u z ↔
            LexEarlier (finiteDummyTailCarrier H n bits) u z) ∧
         ((finiteDummyTailCarrier H n bits).edge 2 u z ↔
            ¬ LexEarlier (finiteDummyTailCarrier H n bits) u z)) := by
  obtain ⟨bits,hFix⟩ :=
    exists_finiteDummyTailOrientation_fixedPoint FH
  refine ⟨bits, ?_⟩
  intro u z hu3 hun huLeaf hzn
  have hUniform := finiteDummyTailCarrier_lex_uniform_tail
    FH bits u n z hun (le_refl n) hzn
  have hBitLex :
      (bits u = true) ↔
        LexEarlier (finiteDummyTailCarrier H n bits) u z :=
    (hFix u hun).trans hUniform
  have hOne :
      (finiteDummyTailCarrier H n bits).edge 1 u z ↔
        LexEarlier (finiteDummyTailCarrier H n bits) u z :=
    (finiteDummyTailCarrier_cross_one_iff
      FH bits u z hu3 hun huLeaf hzn).trans hBitLex
  have hTwoBits :=
    finiteDummyTailCarrier_cross_two_iff
      FH bits u z hu3 hun huLeaf hzn
  have hBool : (bits u = false) ↔ ¬ (bits u = true) := by
    cases h : bits u <;> simp [h]
  exact ⟨hOne,hTwoBits.trans (hBool.trans (not_congr hBitLex))⟩

end DiaryLeafPriority
end ThreeUniformDiaries
