import ThreeUniformDiaries.DiaryCausalLiteralMarkerCompletion
import ThreeUniformDiaries.DiarySourceLexAuxReduction

/-!
# Literal original-branch V3 reduces to meet and split-column preservation

The causal marker completion inserts new cross-branch incidences only
at middle vertices selected by the off-branch mask. In the actual
sign-rooted construction these middle vertices are source LEAVES,
never source 1-splits.

For two source leaves a<b with exact singleton meet m<a, the literal
LexEarlier comparison is decided by the source edges with middle
vertex m, after taking the pointed auxiliary meet of (m,a),(m,b).
Hence if the completed graph preserves the exact singleton meet
and leaves the middle-m column unchanged, the entire literal V3
comparison is preserved, including its RIGHT-bit orientation.

This formalises the precise remaining original-branch obligation:
the causal V3 fixed point already leaves split columns alone, so
the only additional input for the original-branch comparison is
EXACT preservation of their singleton meets. Neither the universal
meet assertion nor full sign-rooted pre-diary is proved here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The pointed auxiliary meet is determined entirely by the
middle-m edge column of the graph, not by its other columns. -/
theorem auxMeetLevel_pointed_eq_of_middle_column
    (R G : Ordered3Graph Nat)
    (m a b : Nat)
    (hCol : ∀ x z : Nat, R.edge x m z ↔ G.edge x m z) :
    R.auxMeetLevel m a m b = G.auxMeetLevel m a m b := by
  classical
  have hType (l : Nat) (hl : l ≤ m) :
      R.SameAuxTypeBelow l m a m b ↔
        G.SameAuxTypeBelow l m a m b := by
    constructor
    · intro h x hx
      exact (hCol x a).symm.trans ((h hx).trans (hCol x b))
    · intro h x hx
      exact (hCol x a).trans ((h hx).trans (hCol x b).symm)
  apply le_antisymm
  · have hBound : R.auxMeetLevel m a m b ≤ m := by
      simpa only [min_self] using R.auxMeetLevel_le_min m a m b
    have hSame : G.SameAuxTypeBelow
        (R.auxMeetLevel m a m b) m a m b :=
      (hType _ hBound).mp (R.auxMeetLevel_agree m a m b)
    have hCap : R.auxMeetLevel m a m b ≤ min m m := by
      simpa only [min_self] using hBound
    exact Nat.le_findGreatest hCap hSame
  · have hBound : G.auxMeetLevel m a m b ≤ m := by
      simpa only [min_self] using G.auxMeetLevel_le_min m a m b
    have hSame : R.SameAuxTypeBelow
        (G.auxMeetLevel m a m b) m a m b :=
      (hType _ hBound).mpr (G.auxMeetLevel_agree m a m b)
    have hCap : G.auxMeetLevel m a m b ≤ min m m := by
      simpa only [min_self] using hBound
    exact Nat.le_findGreatest hCap hSame

/-- With the proper singleton meet preserved, leaving its
middle-m column unchanged forces the exact literal LexEarlier
comparison to be unchanged. No diary axioms are needed. -/
theorem lexEarlier_preserved_of_meet_and_middle_column
    (R G : Ordered3Graph Nat)
    (m a b : Nat)
    (hma : m < a) (hmb : m < b)
    (hMeetR : R.oneMeetLevel a b = m)
    (hMeetG : G.oneMeetLevel a b = m)
    (hCol : ∀ x z : Nat, R.edge x m z ↔ G.edge x m z) :
    LexEarlier R a b ↔ LexEarlier G a b := by
  have hAux : R.auxMeetLevel m a m b =
      G.auxMeetLevel m a m b :=
    auxMeetLevel_pointed_eq_of_middle_column R G m a b hCol
  have hEdge :
      R.edge (R.auxMeetLevel m a m b) m b ↔
        G.edge (G.auxMeetLevel m a m b) m b := by
    rw [hAux]
    exact hCol _ b
  exact (onePass_lexEarlier_iff_mixedAux_right
    R m a b hma hmb hMeetR).trans
      (hEdge.trans
        (onePass_lexEarlier_iff_mixedAux_right
          G m a b hma hmb hMeetG).symm)

/-- At any middle vertex m which the mask never selects, the
literal V3 fixed-point construction preserves the ENTIRE
original edge column, for all first and last vertices. -/
theorem causalMarkerLimit_middle_unmasked
    (R : Ordered3Graph Nat)
    (mask : Nat → Nat → Prop)
    (hMaskLater : ∀ y z, mask y z → y < z)
    (m : Nat)
    (hNoMask : ∀ z : Nat, ¬ mask m z)
    (x z : Nat) :
    (causalMarkerLimit R mask).edge x m z ↔
      R.edge x m z := by
  have hFormula := causalMarkerLimit_formula
    R mask hMaskLater x m z
  have hNo : ¬ mask m z := hNoMask z
  simpa [CausalMarkerColumn, hNo] using hFormula

/-- The concrete causal fixed point preserves the original
LexEarlier sign of any pair whose proper singleton meet is
unchanged and whose meet column is not selected by the mask.

For sign-rooted original branches, a source 1-split m is
automatically unmasked because the mask selects only leaves.
Thus EXACT meet preservation is the outstanding hypothesis. -/
theorem causalMarkerLimit_preserves_original_branch_lex
    (R : Ordered3Graph Nat)
    (mask : Nat → Nat → Prop)
    (hMaskLater : ∀ y z, mask y z → y < z)
    (m a b : Nat)
    (hma : m < a) (hmb : m < b)
    (hMeetR : R.oneMeetLevel a b = m)
    (hMeetG :
      (causalMarkerLimit R mask).oneMeetLevel a b = m)
    (hNoMask : ∀ z : Nat, ¬ mask m z) :
    LexEarlier (causalMarkerLimit R mask) a b ↔
      LexEarlier R a b := by
  have hCol : ∀ x z : Nat,
      R.edge x m z ↔
        (causalMarkerLimit R mask).edge x m z := by
    intro x z
    exact (causalMarkerLimit_middle_unmasked
      R mask hMaskLater m hNoMask x z).symm
  exact (lexEarlier_preserved_of_meet_and_middle_column
    R (causalMarkerLimit R mask) m a b
    hma hmb hMeetR hMeetG hCol).symm

end DiaryLeafPriority
end ThreeUniformDiaries
