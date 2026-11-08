import ThreeUniformDiaries.DiaryCofinalBoundedCountableFusion
import ThreeUniformDiaries.DiaryFiniteNextLeafCoverBounds

/-!
# Cofinal bounded next-leaf horizons are EXACTLY finite next-image covers

The newly merged actual countable fusion endpoint #1201 uses one
numerical upper bound on the new leaf image along cofinally many
finite extension horizons. The earlier conditional fusion criterion
uses a finite W of next-leaf images covering EVERY horizon.

For actual reserved diary stages these are EQUIVALENT:
* cofinal bounded witnesses restrict to each earlier horizon,
  retaining the old supported images and the next leaf value;
* a finite cover W has numerical maximum B and supplies a
  bounded witness at horizon N itself, for every N.

This is a proof at the correct QUANTIFIER LEVEL: the same B is
used at all horizons; merely having an unbounded choice B_n
for each N is not enough (the merged abstract tail-escape
counterexample refutes that inference).

No countable unavoidability, tail-richness, source-specific
relative leaf realization or global coherent embedding is
postulated in the equivalence.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A genuine finite set of candidate images covering EVERY
horizon iff ONE fixed upper bound on next-leaf images occurs at
arbitrarily large horizons, for the SAME old support map f.
Neither hypothesis assumes a coherent infinite extension. -/
theorem finiteHorizonNextLeafCover_iff_cofinal_bounded_images
    (H K : Ordered3Graph Nat) (F f : Nat → Nat) (m : Nat) :
    FiniteHorizonNextLeafCover H K F m f ↔
      HasCofinalBoundedNextLeafImages H K F f m := by
  classical
  constructor
  · rintro ⟨W, hEvery⟩
    let B : Nat := W.sup id
    refine ⟨B, ?_⟩
    intro N
    obtain ⟨g, Q, hOld, hMem⟩ := hEvery N
    refine ⟨N, le_rfl, g, Q, hOld, ?_⟩
    exact Finset.le_sup (f := id) hMem
  · exact finiteHorizonNextLeafCover_of_cofinal_bounded_images
      H K F f m

/-- The cofinal bound introduced in #1201 is also equivalent to
a bound attained at EVERY EXACT horizon. This follows from the
verified cover-vs-bound equivalence together with exact support
restriction and does not assert the bound exists in actual diaries. -/
theorem cofinalBoundedNextLeafImages_iff_allHorizon_uniformBound
    (H K : Ordered3Graph Nat) (F f : Nat → Nat) (m : Nat) :
    HasCofinalBoundedNextLeafImages H K F f m ↔
      ∃ B : Nat, ∀ n : Nat, ∃ g : Nat → Nat,
        ReservedDiaryStage H K F (m + 1 + n) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        g m ≤ B :=
  (finiteHorizonNextLeafCover_iff_cofinal_bounded_images
    H K F f m).symm.trans
      (finiteHorizonNextLeafCover_iff_uniform_image_bound
        H K F m f)

end DiaryLeafPriority
end ThreeUniformDiaries
