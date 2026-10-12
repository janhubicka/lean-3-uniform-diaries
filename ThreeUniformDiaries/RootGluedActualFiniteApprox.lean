import ThreeUniformDiaries.RootGluedAmbientRank
import ThreeUniformDiaries.RootGluedSelectedStem
import Milliken.GeneralTree

/-!
# Exact finite-approximation decoding for actual ATR root-glued type trees

For every genuine scalar Milliken strong subtree having the added
root and synchronized selected coordinate heights, its abstract
first k+1 source levels are literally the root-gluing of the first
k selected levels of the three concrete E0/E1/E2 slices.

This is stronger than a chosen finite code: the equality is valid
for *any* eligible genuine scalar strong subtree, including those
returned by a heterogeneous Milliken theorem. It eliminates an
off-by-one ambiguity and the possibility of an artificial decoder
on finite level carriers. Concrete finite canonical-map data still
must be reconstructed from those slices.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- A strong scalar tree whose first selected ambient level is zero
must contain the actual added root as its selected root. -/
theorem millikenStrong_root_eq_gluedRoot
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (hzero : S.levels 0 = 0) :
    S.root = (⊥ : WithBot CoordNode) := by
  have hrank : rootGluedAmbientTree.level S.root = 0 :=
    S.root_level.trans hzero
  cases h : S.root with
  | none => exact h
  | some z =>
      have hl : rootGluedAmbientTree.level
          (z : WithBot CoordNode) = 0 := by
        simpa only [h] using hrank
      have hp := rootGluedAmbient_level_coe z
      omega

/-- The published r_(k+1) scalar approximation coincides *as a set*
with the glued three-coordinate k-level selected prefix. -/
theorem millikenStrong_initialPart_eq_gluedTruncation
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (f : Nat → Nat)
    (hlevels : S.levels = selectedGluedLevels f)
    (k : Nat) :
    S.initialPart (k + 1) =
      ((TypedVectorSubset.ofGlued S.carrier).truncateSelected f k).glue := by
  let V := TypedVectorSubset.ofGlued S.carrier
  have hroot : S.root = (⊥ : WithBot CoordNode) :=
    millikenStrong_root_eq_gluedRoot S (by
      simpa only [hlevels, selectedGluedLevels_zero])
  ext x
  cases x with
  | none =>
      constructor
      · intro _
        exact (V.truncateSelected f k).root_mem
      · intro _
        have hmem : (⊥ : WithBot CoordNode) ∈ S.carrier := by
          simpa only [hroot] using S.root_mem
        exact ⟨hmem, 0, Nat.zero_lt_succ k,
          by exact rootGluedAmbientTree.level_root⟩
  | some x =>
      constructor
      · rintro ⟨hx, j, hj, hlevel⟩
        cases j with
        | zero =>
            have hzero :
                rootGluedAmbientTree.level (x : WithBot CoordNode) = 0 := by
              simpa only [hlevels, selectedGluedLevels_zero] using hlevel
            have hp := rootGluedAmbient_level_coe x
            omega
        | succ j =>
            have hjk : j < k := by omega
            have hxlevel : level x = f j := by
              rw [hlevels, selectedGluedLevels_succ,
                rootGluedAmbient_level_coe] at hlevel
              omega
            have hV : x ∈ V.carrier (sort x) := ⟨rfl, hx⟩
            exact ((V.truncateSelected f k).some_mem_iff x).mpr
              ⟨hV, j, hjk, hxlevel⟩
      · intro hx
        obtain ⟨hV, j, hjk, hxlevel⟩ :=
          ((V.truncateSelected f k).some_mem_iff x).mp hx
        have hS : (x : WithBot CoordNode) ∈ S.carrier := hV.2
        refine ⟨hS, j + 1, Nat.succ_lt_succ hjk, ?_⟩
        rw [hlevels, selectedGluedLevels_succ,
          rootGluedAmbient_level_coe]
        omega

end CoordNode
end ThreeUniformDiaries
