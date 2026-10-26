import ThreeUniformDiaries.DiaryLexEarlierTypeCongruence

/-!
# Causal V3 marker assignment preserves matching parent singleton types

The earlier sign-rooted gluing lemmas assume an orientation which is
prefix-uniform for ALL later leaves. That condition is stronger than
what V1/V2 actually use. The relevant source pairs have matching
singleton predecessor types, and the off-branch classification for
each earlier middle vertex is the same on both terminals.

Here is the exact causal induction that replaces an orientation
uniformity hypothesis when the new Devlin marker bits are determined
by the LITERAL LexEarlier comparison in the final graph.

The marker formula may refer to the final graph G on its RHS.
No existence of such a G is assumed or proved here: this theorem
asserts that ANY G satisfying the formula along the two chosen
terminal columns preserves their earlier singleton-type equality.
There is no circular proof: at middle vertex y, the lexicographic
decision depends only on previously established type agreement at
strictly earlier middle vertices (< y).

Neither the raw graph R nor the output graph G is required to
already be a diary. This is a local, conditional comparison theorem,
not a finite gluing construction or unrestricted flip absorber.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The actual local marker edge formula. It preserves the raw edge
and adds marker-one/two edges according to the FINAL graph's literal
LexEarlier comparator and a selected off-branch mask. -/
def CausalMarkerColumn
    (R G : Ordered3Graph Nat)
    (mask : Nat → Nat → Prop)
    (x y z : Nat) : Prop :=
  R.edge x y z ∨
    (x = 1 ∧ mask y z ∧ LexEarlier G y z) ∨
    (x = 2 ∧ mask y z ∧ ¬ LexEarlier G y z)

/-- Equality of the mask for two terminal leaves at each earlier
middle column. It is the exact algebraic hypothesis supplied by
the sign-rooted off-branch prefix classification. -/
def SameEarlierMarkerMask
    (mask : Nat → Nat → Prop)
    (s u v : Nat) : Prop :=
  ∀ y : Nat, y < s → (mask y u ↔ mask y v)

/-- Causal marker transport of the full predecessor singleton type.

If the raw relation has matching singleton types below s, the
off-branch masks agree for those earlier columns, and the output
graph adds exactly the literal lexicographically chosen marker edges,
then the OUTPUT relation has matching singleton types below s.

Unlike the earlier prefix-uniformity assumption, this requires no
orientation comparison for arbitrary pairs of later vertices.
-/
theorem causalMarker_preserves_parent_oneType
    (R G : Ordered3Graph Nat)
    (mask : Nat → Nat → Prop)
    (s u v : Nat)
    (hsu : s ≤ u) (hsv : s ≤ v)
    (hRaw : R.SameOneTypeBelow s u v)
    (hMask : SameEarlierMarkerMask mask s u v)
    (hU : ∀ x y : Nat, x < y → y < s →
      (G.edge x y u ↔ CausalMarkerColumn R G mask x y u))
    (hV : ∀ x y : Nat, x < y → y < s →
      (G.edge x y v ↔ CausalMarkerColumn R G mask x y v)) :
    G.SameOneTypeBelow s u v := by
  have hAt :
      ∀ y : Nat, y < s → ∀ x : Nat, x < y →
        (G.edge x y u ↔ G.edge x y v) := by
    intro y
    induction y using Nat.strong_induction_on with
    | h y ih =>
      intro hys x hxy
      have hEarlier : G.SameOneTypeBelow y u v := by
        intro a b hab hby
        exact ih b hby (lt_trans hby hys) a hab
      have hLex : LexEarlier G y u ↔ LexEarlier G y v :=
        lexEarlier_right_congr_of_sameOneType
          G y y u v le_rfl (by omega) (by omega) hEarlier
      have hMark : mask y u ↔ mask y v := hMask y hys
      have hOne :
          (x = 1 ∧ mask y u ∧ LexEarlier G y u) ↔
            (x = 1 ∧ mask y v ∧ LexEarlier G y v) :=
        and_congr Iff.rfl (and_congr hMark hLex)
      have hTwo :
          (x = 2 ∧ mask y u ∧ ¬ LexEarlier G y u) ↔
            (x = 2 ∧ mask y v ∧ ¬ LexEarlier G y v) :=
        and_congr Iff.rfl (and_congr hMark (not_congr hLex))
      have hOld : R.edge x y u ↔ R.edge x y v :=
        hRaw hxy hys
      have hFormula :
          CausalMarkerColumn R G mask x y u ↔
            CausalMarkerColumn R G mask x y v := by
        unfold CausalMarkerColumn
        exact or_congr hOld (or_congr hOne hTwo)
      exact (hU x y hxy hys).trans
        (hFormula.trans (hV x y hxy hys).symm)
  intro x y hxy hys
  exact hAt y hys x hxy

end DiaryLeafPriority
end ThreeUniformDiaries
