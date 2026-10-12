import ThreeUniformDiaries.ScalarFiniteCodeIntrinsic

/-!
# Canonical strictly increasing extension of finite ATR source heights

An actual Milliken finite approximation of height k+2 determines
precisely the k+1 selected E0/E1/E2 coordinate heights; it cannot
determine any later selected height of an infinite realizer.

For the finite canonical-map API, which expects Nat → Nat, extend
these *intrinsic finite* heights by adding successive integers after
the last height. This is a definition on the finite approximation
itself, completely independent of any further infinite strong tree
or choices of future gaps.

The strictly increasing and agreement properties below allow the
genuine finite strong-picture fields to be transported to this
canonical function using finiteStrongPicture_congr_finite_levels.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree
open ThreeUniformDiaries.CoordNode

/-- Intrinsic finite source heights are strictly increasing. -/
theorem finiteCoordinateHeights_strictMono
    (k : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2)) :
    StrictMono (finiteCoordinateHeights k a) := by
  intro i j hij
  let S : StrongSubtree CoordNode.rootGluedAmbientTree :=
    Classical.choose a.realised
  have hS : a.carrier = S.initialPart (k + 2) :=
    Classical.choose_spec a.realised
  have hei := finiteCoordinateHeights_eq_realizer k a S hS i
  have hej := finiteCoordinateHeights_eq_realizer k a S hS j
  have hlt : i.val + 1 < j.val + 1 := by omega
  have hlevels := S.levels_strictMono hlt
  have hpos : 0 < S.levels (i.val + 1) := by
    have h := S.levels_strictMono (Nat.zero_lt_succ i.val)
    exact lt_of_le_of_lt (Nat.zero_le _) h
  rw [hei, hej]
  change S.levels (i.val + 1) - 1 <
    S.levels (j.val + 1) - 1
  omega

/-- A fixed canonical extension after the last finite coordinate
height. The infinite tail has no mathematical relevance to the
underlying height-(k+1) finite code. -/
noncomputable def canonicalFiniteLevelMap
    (k : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (i : Nat) : Nat :=
  if h : i ≤ k then
    finiteCoordinateHeights k a ⟨i, Nat.lt_succ_of_le h⟩
  else
    finiteCoordinateHeights k a ⟨k, Nat.lt_succ_self k⟩ + (i - k)

theorem canonicalFiniteLevelMap_inside
    (k : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (i : Nat) (hi : i ≤ k) :
    canonicalFiniteLevelMap k a i =
      finiteCoordinateHeights k a ⟨i, Nat.lt_succ_of_le hi⟩ := by
  simp only [canonicalFiniteLevelMap, dif_pos hi]

theorem canonicalFiniteLevelMap_outside
    (k : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (i : Nat) (hi : k < i) :
    canonicalFiniteLevelMap k a i =
      finiteCoordinateHeights k a ⟨k, Nat.lt_succ_self k⟩ + (i - k) := by
  simp only [canonicalFiniteLevelMap, dif_neg (Nat.not_le.mpr hi)]

/-- The intrinsically determined infinite extension is strictly
increasing, even when the original finite gaps were unbounded. -/
theorem canonicalFiniteLevelMap_strictMono
    (k : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2)) :
    StrictMono (canonicalFiniteLevelMap k a) := by
  intro i j hij
  by_cases hj : j ≤ k
  · have hi : i ≤ k := by omega
    rw [canonicalFiniteLevelMap_inside k a i hi,
      canonicalFiniteLevelMap_inside k a j hj]
    apply finiteCoordinateHeights_strictMono k a
    change i < j
    exact hij
  · have hj' : k < j := Nat.lt_of_not_ge hj
    by_cases hi : i ≤ k
    · rw [canonicalFiniteLevelMap_inside k a i hi,
        canonicalFiniteLevelMap_outside k a j hj']
      have hle :
          finiteCoordinateHeights k a
              ⟨i, Nat.lt_succ_of_le hi⟩ ≤
          finiteCoordinateHeights k a
              ⟨k, Nat.lt_succ_self k⟩ := by
        apply (finiteCoordinateHeights_strictMono k a).monotone
        change i ≤ k
        exact hi
      omega
    · have hi' : k < i := Nat.lt_of_not_ge hi
      rw [canonicalFiniteLevelMap_outside k a i hi',
        canonicalFiniteLevelMap_outside k a j hj']
      omega

/-- Every genuine infinite realizer agrees with the canonical
finite-height level map throughout its finite selected prefix. -/
theorem canonicalFiniteLevelMap_eq_realizer
    (k : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (S : StrongSubtree CoordNode.rootGluedAmbientTree)
    (hS : a.carrier = S.initialPart (k + 2))
    (i : Nat) (hi : i ≤ k) :
    canonicalFiniteLevelMap k a i =
      CoordNode.millikenCoordinateLevels S i := by
  calc
    canonicalFiniteLevelMap k a i =
        finiteCoordinateHeights k a ⟨i, Nat.lt_succ_of_le hi⟩ :=
      canonicalFiniteLevelMap_inside k a i hi
    _ = CoordNode.millikenCoordinateLevels S i :=
      finiteCoordinateHeights_eq_realizer k a S hS
        ⟨i, Nat.lt_succ_of_le hi⟩

end ATRFiniteDecoder
end ThreeUniformDiaries
