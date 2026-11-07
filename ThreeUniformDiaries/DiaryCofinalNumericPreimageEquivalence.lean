import ThreeUniformDiaries.DiaryFixedProfileUniformBoundCriterion
import ThreeUniformDiaries.DiaryUpperBoundCofinalNumericLeafBounds

/-!
# Cofinal next-leaf numerical bounds IFF bounded preimage indices

The previously checked cofinal finite-cover sharp diary upper
interface was phrased with numerical bounds on next target leaf
images. The bounded PREIMAGE INDEX criterion was previously only
known to be sufficient.

The reverse also holds, without assuming the external leaf map
F is increasing or injective: every genuine reserved stage has
its selected next leaf image IN the prescribed range. If it is
numerically ≤ B, the FINITE target set [0,B] admits a uniformly
bounded chosen preimage section. This bound can be selected
AFTER the cofinal refinement but BEFORE all future horizons.

These are exact equivalences of CONDITIONAL hypotheses.
Nothing proves those hypotheses from diary genericity or
finite flip absorption, and no countable diary theorem is
unconditionally asserted.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- The two cofinal next-leaf boundedness hypotheses are in
fact EQUIVALENT: uniform image bounds and uniformly bounded
chosen preimage indices. The same outer subcopy w₀ and
refinement i work in both directions. -/
theorem cofinal_uniformImageBounds_iff_boundedPreimageIndices
    {U H : Ordered3Graph Nat}
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H) :
    HasCofinalUniformNextImageBounds D F ↔
      HasCofinalBoundedNextLeafRangeIndices D F := by
  classical
  constructor
  · intro hBound w₀
    obtain ⟨i, hRefined⟩ := hBound w₀
    refine ⟨i, ?_⟩
    intro m hm f hf
    obtain ⟨B, hEvery⟩ := hRefined m hm f hf
    let R : Nat → Nat := fun t => F (w₀ (i t))
    obtain ⟨T, hSection⟩ :=
      bounded_range_values_have_bounded_preimage_indices R B
    refine ⟨T, ?_⟩
    intro n
    obtain ⟨g, Q, hCompat, hNumeric⟩ := hEvery n
    have hmSupported :
        m ∈ countableDiaryFiniteSupport H (m + 1 + n) := by
      exact mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H (m + 1 + n)) m
        ((mem_countableDiaryLeafPrefix_iff H (m + 1 + n) m).mpr
          ⟨hm.1, by omega, hm⟩)
    obtain ⟨t, hRange⟩ := Q.1.leaf_range m hmSupported hm
    have hInR : ∃ t : Nat, R t = g m := ⟨t, hRange.symm⟩
    obtain ⟨t', ht', htEq⟩ :=
      hSection (g m) hNumeric hInR
    exact ⟨g, Q, hCompat, t', ht', htEq.symm⟩
  · intro hIndex w₀
    obtain ⟨i, hRefined⟩ := hIndex w₀
    refine ⟨i, ?_⟩
    intro m hm f hf
    obtain ⟨T, hEvery⟩ := hRefined m hm f hf
    let R : Nat → Nat := fun t => F (w₀ (i t))
    refine ⟨(Finset.range T).sup R, ?_⟩
    intro n
    obtain ⟨g, Q, hCompat, t, ht, hEq⟩ := hEvery n
    refine ⟨g, Q, hCompat, ?_⟩
    rw [hEq]
    exact Finset.le_sup (f := R) (Finset.mem_range.mpr ht)

/-- The cofinal finite SET cover condition for all persistent
leaf stages is equivalent to a uniform bound on chosen target
leaf preimage indices. It is not merely implied by that bound. -/
theorem cofinal_finiteCovers_iff_boundedPreimageIndices
    {U H : Ordered3Graph Nat}
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H) :
    HasCofinalPersistentFiniteNextLeafCovers D F ↔
      HasCofinalBoundedNextLeafRangeIndices D F :=
  (cofinalFiniteCover_iff_uniformNextImageBound D F).trans
    (cofinal_uniformImageBounds_iff_boundedPreimageIndices D F)

end ATRFiniteDecoder
end ThreeUniformDiaries
