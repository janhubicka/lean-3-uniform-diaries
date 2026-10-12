import ThreeUniformDiaries.RootGluedActualFiniteApprox

/-!
# Normalize an arbitrary actual rooted scalar strong subtree to three
# synchronized E0/E1/E2 selected coordinate levels

No extra level-selection hypothesis is imposed on Milliken's witness.
If the new added scalar root is retained (as it is in the protected-stem
neighbourhood), removing the scalar offset 1 from all later source
levels yields a strictly increasing coordinate-level function.

This makes the exact finite-prefix decoding theorem applicable to
*every* scalar strong refinement returned by general-tree Milliken.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The coordinate level map obtained by discarding the additional
root and subtracting its one-level ambient offset. -/
def millikenCoordinateLevels
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (i : Nat) : Nat :=
  S.levels (i + 1) - 1

/-- The arbitrary scalar level selection still gives a genuinely
strictly increasing synchronized coordinate level map. -/
theorem millikenCoordinateLevels_strictMono
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (hzero : S.levels 0 = 0) :
    StrictMono (millikenCoordinateLevels S) := by
  intro i j hij
  have hlevels :=
    S.levels_strictMono (Nat.add_lt_add_right hij 1)
  have hpositive : 0 < S.levels (i + 1) := by
    have h := S.levels_strictMono (Nat.zero_lt_succ i)
    rw [hzero] at h
    exact h
  change S.levels (i + 1) - 1 < S.levels (j + 1) - 1
  omega

/-- Scalar selected levels are *exactly* the root-adjoined coordinate
selected levels, no extra normalization axiom or choice. -/
theorem millikenLevels_eq_selectedGluedLevels
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (hzero : S.levels 0 = 0) :
    S.levels = selectedGluedLevels (millikenCoordinateLevels S) := by
  funext n
  cases n with
  | zero =>
      simpa only [selectedGluedLevels_zero] using hzero
  | succ n =>
      have hpositive : 0 < S.levels (n + 1) := by
        have h := S.levels_strictMono (Nat.zero_lt_succ n)
        rw [hzero] at h
        exact h
      change S.levels (n + 1) =
        (S.levels (n + 1) - 1) + 1
      omega

/-- If the scalar strong tree is rooted at the genuinely adjoined
root, its selected source height zero is ambient height zero. -/
theorem millikenStrong_levels_zero_of_root
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (hroot : S.root = (none : WithBot CoordNode)) :
    S.levels 0 = 0 := by
  have h := S.root_level
  rw [hroot] at h
  have h0 := rootGluedAmbientTree.level_root
  omega

/-- Every scalar strong subtree with the added root admits the exact
finite coordinate prefix presentation, even if its later selected
levels have arbitrary gaps and unbounded branching. -/
theorem millikenStrong_normalized_finitePrefix
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (hroot : S.root = (none : WithBot CoordNode))
    (k : Nat) :
    S.initialPart (k + 1) =
      ((TypedVectorSubset.ofGlued S.carrier).truncateSelected
        (millikenCoordinateLevels S) k).glue := by
  exact millikenStrong_initialPart_eq_gluedTruncation S
    (millikenCoordinateLevels S)
    (millikenLevels_eq_selectedGluedLevels S
      (millikenStrong_levels_zero_of_root S hroot)) k

end CoordNode
end ThreeUniformDiaries
