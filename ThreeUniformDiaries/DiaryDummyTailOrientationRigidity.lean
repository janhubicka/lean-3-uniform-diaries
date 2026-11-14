import ThreeUniformDiaries.DiaryFiniteDummyTailPrediary
import Lean.Elab.Tactic.Omega

/-!
# Track B: the Devlin V3 equations force all genuine old-to-tail bits

The dummy-tail carrier depends on its Boolean orientation only at
GENUINE OLD LEAVES u<n. Its old edge columns are independent of bits.
Its tail endpoint column below u reads only bits at earlier old leaves.
Thus the literal LexEarlier comparison of u with the first tail leaf
is causal even if unrelated assignments disagree at nonleaf levels.

If TWO dummy-tail carriers for the same finite V/E prediary are both
actual global RolePrediaries, V3 and the marker-one equation force
their old leaf bits to agree by strong induction. Consequently their
entire ternary edge predicates agree, including all old/tail tests.

This excludes arbitrary freedom to optimize an event-free cut by
changing globally valid V3 orientation bits. It is NOT existence of a
protected relative prediary, a recursive absorber or countable flip
absorption; V3 uniqueness is a necessary *rigidity* theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat} {n : Nat}

/-- The old-to-tail LexEarlier test at old u ignores all nonleaf
orientation bits and depends on old genuine leaf bits only at t<u.
This improves the previously verified all-prior-bits causality
to the exact edge support of the actual dummy-tail carrier. -/
theorem finiteDummyTailCarrier_lex_prefix_congr_of_leafBits
    (FH : FiniteDiaryEdgeFrame H n)
    (f g : Nat → Bool) (u : Nat) (hun : u < n)
    (hBefore : ∀ t : Nat, 3 ≤ t → t < u →
      IsLeaf H t → f t = g t) :
    LexEarlier (finiteDummyTailCarrier H n f) u n ↔
      LexEarlier (finiteDummyTailCarrier H n g) u n := by
  have hOld : ∀ a b : Nat, a < b → b < u →
      ((finiteDummyTailCarrier H n f).edge a b u ↔
       (finiteDummyTailCarrier H n g).edge a b u) := by
    intro a b hab hb
    exact
      (finiteDummyTailCarrier_finite_edge_iff FH f a b u hun).trans
        (finiteDummyTailCarrier_finite_edge_iff FH g a b u hun).symm
  have hTail : ∀ a b : Nat, a < b → b < u →
      ((finiteDummyTailCarrier H n f).edge a b n ↔
       (finiteDummyTailCarrier H n g).edge a b n) := by
    intro a b _hab hbu
    have hbn : b < n := by omega
    calc
      (finiteDummyTailCarrier H n f).edge a b n ↔
        (3 ≤ b ∧ IsLeaf H b ∧
          ((a = 1 ∧ f b = true) ∨
           (a = 2 ∧ f b = false))) :=
          finiteDummyTailCarrier_tail_column_iff
            f a b n hbn (le_refl n)
      _ ↔
        (3 ≤ b ∧ IsLeaf H b ∧
          ((a = 1 ∧ g b = true) ∨
           (a = 2 ∧ g b = false))) := by
          by_cases hb3 : 3 ≤ b
          · by_cases hLeaf : IsLeaf H b
            · rw [hBefore b hb3 hbu hLeaf]
            · simp [hLeaf]
          · simp [hb3]
      _ ↔ (finiteDummyTailCarrier H n g).edge a b n :=
          (finiteDummyTailCarrier_tail_column_iff
            g a b n hbn (le_refl n)).symm
  exact lexEarlier_prefix_congr_of_edge_columns
    (H := finiteDummyTailCarrier H n f)
    (K := finiteDummyTailCarrier H n g)
    u n hun hOld hTail

/-- For any fixed finite V/E prediary, the globally valid
dummy-tail RolePrediary has a UNIQUE orientation on every genuine
old leaf. Values of the supplied bit function at nonleaf levels
are irrelevant and need not be equal. -/
theorem finiteDummyTail_valid_prediaries_agree_oldLeaf_bits
    (P : FiniteRolePrediaryBlock H n)
    (f g : Nat → Bool)
    (PF : RolePrediary (finiteDummyTailCarrier H n f))
    (PG : RolePrediary (finiteDummyTailCarrier H n g)) :
    ∀ u : Nat, u < n → IsLeaf H u → f u = g u := by
  classical
  intro u
  induction u using Nat.strong_induction_on with
  | h u ih =>
    intro hun hLeaf
    have hBefore : ∀ t : Nat, 3 ≤ t → t < u →
        IsLeaf H t → f t = g t := by
      intro t _ht3 htu htLeaf
      exact ih t htu (by omega) htLeaf
    have hLex :
        LexEarlier (finiteDummyTailCarrier H n f) u n ↔
          LexEarlier (finiteDummyTailCarrier H n g) u n :=
      finiteDummyTailCarrier_lex_prefix_congr_of_leafBits
        P.frame f g u hun hBefore
    have hLF : IsLeaf (finiteDummyTailCarrier H n f) u :=
      (finiteDummyTailCarrier_old_leaf_iff
        P.frame f u hun).mpr hLeaf
    have hLG : IsLeaf (finiteDummyTailCarrier H n g) u :=
      (finiteDummyTailCarrier_old_leaf_iff
        P.frame g u hun).mpr hLeaf
    have hNF : IsLeaf (finiteDummyTailCarrier H n f) n :=
      finiteDummyTailCarrier_tail_isLeaf P.frame f n (le_refl n)
    have hNG : IsLeaf (finiteDummyTailCarrier H n g) n :=
      finiteDummyTailCarrier_tail_isLeaf P.frame g n (le_refl n)
    have hF :
        (f u = true) ↔
          LexEarlier (finiteDummyTailCarrier H n f) u n := by
      exact
        (finiteDummyTailCarrier_cross_one_iff
          P.frame f u n hLeaf.1 hun hLeaf (le_refl n)).symm.trans
          (PF.leaf_marker_one u n hun hLF hNF)
    have hG :
        (g u = true) ↔
          LexEarlier (finiteDummyTailCarrier H n g) u n := by
      exact
        (finiteDummyTailCarrier_cross_one_iff
          P.frame g u n hLeaf.1 hun hLeaf (le_refl n)).symm.trans
          (PG.leaf_marker_one u n hun hLG hNG)
    have hBits : (f u = true) ↔ (g u = true) :=
      hF.trans (hLex.trans hG.symm)
    cases hf : f u <;> cases hg : g u <;> simp_all [hf, hg]

/-- The entire concrete carriers of two valid dummy-tail prediaries
have literally the same edge and nonedge predicate on ALL triples,
even though values at nonleaf/unused Boolean coordinates may differ. -/
theorem finiteDummyTail_valid_prediaries_same_edges
    (P : FiniteRolePrediaryBlock H n)
    (f g : Nat → Bool)
    (PF : RolePrediary (finiteDummyTailCarrier H n f))
    (PG : RolePrediary (finiteDummyTailCarrier H n g)) :
    ∀ x y z : Nat,
      ((finiteDummyTailCarrier H n f).edge x y z ↔
       (finiteDummyTailCarrier H n g).edge x y z) := by
  have hLeafBits :=
    finiteDummyTail_valid_prediaries_agree_oldLeaf_bits P f g PF PG
  intro x y z
  constructor
  · intro he
    rcases he with hOld | hCross | hTail
    · exact Or.inl hOld
    · obtain ⟨u,hu3,hun,hLeaf,hzn,hy,hBit⟩ := hCross
      have hEq : f u = g u := hLeafBits u hun hLeaf
      have hBitEq :
          ((x = 1 ∧ f u = true) ∨ (x = 2 ∧ f u = false)) ↔
            ((x = 1 ∧ g u = true) ∨ (x = 2 ∧ g u = false)) := by
        rw [hEq]
      exact Or.inr (Or.inl
        ⟨u,hu3,hun,hLeaf,hzn,hy,hBitEq.mp hBit⟩)
    · exact Or.inr (Or.inr hTail)
  · intro he
    rcases he with hOld | hCross | hTail
    · exact Or.inl hOld
    · obtain ⟨u,hu3,hun,hLeaf,hzn,hy,hBit⟩ := hCross
      have hEq : f u = g u := hLeafBits u hun hLeaf
      have hBitEq :
          ((x = 1 ∧ f u = true) ∨ (x = 2 ∧ f u = false)) ↔
            ((x = 1 ∧ g u = true) ∨ (x = 2 ∧ g u = false)) := by
        rw [hEq]
      exact Or.inr (Or.inl
        ⟨u,hu3,hun,hLeaf,hzn,hy,hBitEq.mpr hBit⟩)
    · exact Or.inr (Or.inr hTail)

end DiaryLeafPriority
end ThreeUniformDiaries
