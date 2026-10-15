import ThreeUniformDiaries.DiaryFiniteThreeTailAmalgam
import ThreeUniformDiaries.ActualFiniteEmbeddingMeets

/-!
# Finite ATR survives inserting the negative exterior leaf

The second three-tail picture is included into the four-tail free
amalgam by the one-position shift. Its only potentially problematic
selected singleton cut is n+1, mapped to n+2: the inserted leaf can
alter singleton types at an unselected intermediate level.

For a genuine split pair this obstruction disappears, because the
two original leaves are already distinguished BELOW cut n+1.
At cuts <= n the map fixes every earlier witness. At cut n+1,
the only two distinct remaining vertices are precisely those leaves.
There is only one ordered exterior pair, so the auxiliary-type
condition beyond n is tautological.

These are the exact finite ATR conditions, NOT a false claim about
the infinitely continued source or about convexity of the embedding.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- An induced finite one-position shift is an auxiliary-type-
respecting finite embedding when the two exterior leaves already
have distinct singleton types by the split. The target has no
restriction on edges involving the newly inserted vertex. -/
theorem finiteAuxEmbedding_threeTailShift_of_split_distinction
    (B C : Ordered3Graph Nat) (n : Nat)
    (hEdge : ∀ x y z, x < y → y < z → z < n+3 →
      (B.edge x y z ↔
       C.edge (threeTailShift n x) (threeTailShift n y)
         (threeTailShift n z)))
    (hSep : ¬ B.SameOneTypeBelow (n+1) (n+1) (n+2)) :
    FiniteAuxEmbedding B C (threeTailShift n) (n+3) := by
  have hTargetSep :
      ¬ C.SameOneTypeBelow (n+2) (n+2) (n+3) := by
    intro ht
    apply hSep
    intro x y hxy hy
    have hx : x ≤ n := by omega
    have hy' : y ≤ n := by omega
    have hU : B.edge x y (n+1) ↔ C.edge x y (n+2) := by
      simpa only [threeTailShift_prefix n x hx,
        threeTailShift_prefix n y hy',
        threeTailShift_firstLeaf n] using
        (hEdge x y (n+1) hxy (by omega) (by omega))
    have hV : B.edge x y (n+2) ↔ C.edge x y (n+3) := by
      simpa only [threeTailShift_prefix n x hx,
        threeTailShift_prefix n y hy',
        threeTailShift_secondLeaf n] using
        (hEdge x y (n+2) hxy (by omega) (by omega))
    exact hU.trans ((ht hxy (by omega)).trans hV.symm)
  have hSepRev : ¬ B.SameOneTypeBelow (n+1) (n+2) (n+1) := by
    intro hs
    apply hSep
    intro x y hxy hy
    exact (hs hxy hy).symm
  have hTargetSepRev :
      ¬ C.SameOneTypeBelow (n+2) (n+3) (n+2) := by
    intro hs
    apply hTargetSep
    intro x y hxy hy
    exact (hs hxy hy).symm
  refine {
    strictMono := threeTailShift_strictMono n
    edge_iff := hEdge
    one := ?_
    aux := ?_
  }
  · intro w u v hwu hwv hu hv
    by_cases hw : w ≤ n
    · have hwf : threeTailShift n w = w :=
        threeTailShift_prefix n w hw
      constructor
      · intro hs x y hxy hy
        have hyw : y < w := by simpa only [hwf] using hy
        have hx : x ≤ n := by omega
        have hy' : y ≤ n := by omega
        have hU : B.edge x y u ↔
            C.edge x y (threeTailShift n u) := by
          simpa only [threeTailShift_prefix n x hx,
            threeTailShift_prefix n y hy'] using
              (hEdge x y u hxy (by omega) hu)
        have hV : B.edge x y v ↔
            C.edge x y (threeTailShift n v) := by
          simpa only [threeTailShift_prefix n x hx,
            threeTailShift_prefix n y hy'] using
              (hEdge x y v hxy (by omega) hv)
        exact hU.symm.trans ((hs hxy hyw).trans hV)
      · intro ht x y hxy hy
        have hyw : y < threeTailShift n w := by
          simpa only [hwf] using hy
        have hx : x ≤ n := by omega
        have hy' : y ≤ n := by omega
        have hU : B.edge x y u ↔
            C.edge x y (threeTailShift n u) := by
          simpa only [threeTailShift_prefix n x hx,
            threeTailShift_prefix n y hy'] using
              (hEdge x y u hxy (by omega) hu)
        have hV : B.edge x y v ↔
            C.edge x y (threeTailShift n v) := by
          simpa only [threeTailShift_prefix n x hx,
            threeTailShift_prefix n y hy'] using
              (hEdge x y v hxy (by omega) hv)
        exact hU.trans ((ht hxy hyw).trans hV.symm)
    · have hCases :
          u = v ∨
          (w = n+1 ∧ u = n+1 ∧ v = n+2) ∨
          (w = n+1 ∧ u = n+2 ∧ v = n+1) := by
        omega
      rcases hCases with heq | hpos | hneg
      · subst v
        constructor
        · intro _ x y hxy hy
          rfl
        · intro _ x y hxy hy
          rfl
      · rcases hpos with ⟨rfl, rfl, rfl⟩
        simpa only [threeTailShift_firstLeaf,
          threeTailShift_secondLeaf] using
            (iff_of_false hSep hTargetSep)
      · rcases hneg with ⟨rfl, rfl, rfl⟩
        simpa only [threeTailShift_firstLeaf,
          threeTailShift_secondLeaf] using
            (iff_of_false hSepRev hTargetSepRev)
  · intro w u₀ u₁ v₀ v₁ hwu hu hvw hv hu₁ hv₁
    by_cases hw : w ≤ n
    · have hwf : threeTailShift n w = w :=
        threeTailShift_prefix n w hw
      constructor
      · intro hs x hx
        have hxw : x < w := by simpa only [hwf] using hx
        have hx' : x ≤ n := by omega
        have hU : B.edge x u₀ u₁ ↔
            C.edge x (threeTailShift n u₀)
              (threeTailShift n u₁) := by
          simpa only [threeTailShift_prefix n x hx'] using
            (hEdge x u₀ u₁ (by omega) hu hu₁)
        have hV : B.edge x v₀ v₁ ↔
            C.edge x (threeTailShift n v₀)
              (threeTailShift n v₁) := by
          simpa only [threeTailShift_prefix n x hx'] using
            (hEdge x v₀ v₁ (by omega) hv hv₁)
        exact hU.symm.trans ((hs hxw).trans hV)
      · intro ht x hx
        have hxw : x < threeTailShift n w := by
          simpa only [hwf] using hx
        have hx' : x ≤ n := by omega
        have hU : B.edge x u₀ u₁ ↔
            C.edge x (threeTailShift n u₀)
              (threeTailShift n u₁) := by
          simpa only [threeTailShift_prefix n x hx'] using
            (hEdge x u₀ u₁ (by omega) hu hu₁)
        have hV : B.edge x v₀ v₁ ↔
            C.edge x (threeTailShift n v₀)
              (threeTailShift n v₁) := by
          simpa only [threeTailShift_prefix n x hx'] using
            (hEdge x v₀ v₁ (by omega) hv hv₁)
        exact hU.trans ((ht hxw).trans hV.symm)
    · have hPairs :
          u₀ = n+1 ∧ u₁ = n+2 ∧
          v₀ = n+1 ∧ v₁ = n+2 := by omega
      rcases hPairs with ⟨rfl, rfl, rfl, rfl⟩
      constructor
      · intro _ x hx
        rfl
      · intro _ x hx
        rfl

/-- The first three-tail picture is the literal initial segment
of the four-tail amalgam, hence its finite ATR inclusion is the
identity without ANY extra compatibility hypothesis. -/
theorem threeTailFreeAmalgam_left_finiteAuxEmbedding
    (A B : Ordered3Graph Nat) (n : Nat) :
    FiniteAuxEmbedding A (threeTailFreeAmalgam A B n) id (n+3) := by
  refine {
    strictMono := by intro a b hab; exact hab
    edge_iff := ?_
    one := ?_
    aux := ?_
  }
  · intro a b c hab hbc hc
    exact (threeTailFreeAmalgam_left A B n a b c hc).symm
  · intro w u v hwu hwv hu hv
    constructor
    · intro hs x y hxy hy
      exact (threeTailFreeAmalgam_left A B n x y u hu).trans
        ((hs hxy hy).trans (threeTailFreeAmalgam_left A B n x y v hv).symm)
    · intro ht x y hxy hy
      exact (threeTailFreeAmalgam_left A B n x y u hu).symm.trans
        ((ht hxy hy).trans
          (threeTailFreeAmalgam_left A B n x y v hv))
  · intro w u₀ u₁ v₀ v₁ hwu hu hvw hv hu₁ hv₁
    constructor
    · intro hs x hx
      exact (threeTailFreeAmalgam_left A B n x u₀ u₁ hu₁).trans
        ((hs hx).trans (threeTailFreeAmalgam_left A B n x v₀ v₁ hv₁).symm)
    · intro ht x hx
      exact (threeTailFreeAmalgam_left A B n x u₀ u₁ hu₁).symm.trans
        ((ht hx).trans
          (threeTailFreeAmalgam_left A B n x v₀ v₁ hv₁))

/-- The *right* three-tail finite source remains a genuine
finite ATR embedding of the four-tail free amalgam under the
single necessary split-distinction hypothesis. -/
theorem threeTailFreeAmalgam_right_finiteAuxEmbedding
    (A B : Ordered3Graph Nat) (n : Nat)
    (hOverlap : ThreeTailOverlapCompatible A B n)
    (hSep : ¬ B.SameOneTypeBelow (n+1) (n+1) (n+2)) :
    FiniteAuxEmbedding B (threeTailFreeAmalgam A B n)
      (threeTailShift n) (n+3) := by
  apply finiteAuxEmbedding_threeTailShift_of_split_distinction
    B (threeTailFreeAmalgam A B n) n
  · intro x y z hxy hyz hz
    exact (threeTailFreeAmalgam_right A B n hOverlap
      x y z hxy hyz hz).symm
  · exact hSep

/-- Exact leaf-pair singleton meet at the split supplies the
necessary distinction; no separate cross-edge axiom is needed. -/
theorem threeTailFreeAmalgam_right_finiteAuxEmbedding_of_meet
    (A B : Ordered3Graph Nat) (n : Nat)
    (hOverlap : ThreeTailOverlapCompatible A B n)
    (hMeet : B.oneMeetLevel (n+1) (n+2) = n) :
    FiniteAuxEmbedding B (threeTailFreeAmalgam A B n)
      (threeTailShift n) (n+3) := by
  classical
  apply threeTailFreeAmalgam_right_finiteAuxEmbedding A B n hOverlap
  intro h
  have hb : n+1 ≤ B.oneMeetLevel (n+1) (n+2) :=
    Nat.le_findGreatest (by omega) h
  omega

end Ordered3Graph
end ThreeUniformDiaries
