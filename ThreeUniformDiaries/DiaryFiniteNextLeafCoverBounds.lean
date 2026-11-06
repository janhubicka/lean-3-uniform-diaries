import ThreeUniformDiaries.DiaryFiniteCandidatePersistentFusion

/-!
# The exact boundedness content of a finite next-leaf cover

Track D's finite-horizon persistence theorem uses a genuinely
FINITE set W of possible next-leaf images at every later finite
horizon. The condition is exactly equivalent to a uniform
numerical upper bound B on a next-leaf image at every horizon.
It is not enough to bound the old-new singleton MEET level:
the actual next leaf may escape to infinity while its
meet with a previously selected leaf remains fixed.

A useful sufficient condition for a prescribed leaf range
F[Nat] is instead a uniform bound on the PREIMAGE INDEX t
of the new leaf, since the images F[0..B) form a finite set.
No monotonicity of F is needed, and the current theorem does
not assert such a bound exists for arbitrary diary targets.

This is a purely finite combinatorial bridge for the next
mathematical Track D role-sensitive realization attack.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- At an actual reserved leaf extension, a genuinely finite
next-image cover is equivalent to a uniform Nat bound on
the target vertex image of the new source leaf.
The finite witnesses g at different horizons may differ. -/
theorem finiteHorizonNextLeafCover_iff_uniform_image_bound
    (H K : Ordered3Graph Nat) (F : Nat → Nat)
    (m : Nat) (f : Nat → Nat) :
    FiniteHorizonNextLeafCover H K F m f ↔
    ∃ B : Nat, ∀ n : Nat, ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1 + n) g ∧
      CofinalDiaryStageCompatible H m f g ∧
      g m ≤ B := by
  classical
  constructor
  · rintro ⟨W, hCover⟩
    let B : Nat := W.sup id
    refine ⟨B, ?_⟩
    intro n
    obtain ⟨g, hReserved, hOld, hMem⟩ := hCover n
    refine ⟨g, hReserved, hOld, ?_⟩
    exact Finset.le_sup (f := id) hMem
  · rintro ⟨B, hBound⟩
    refine ⟨Finset.range (B + 1), ?_⟩
    intro n
    obtain ⟨g, hReserved, hOld, hImage⟩ := hBound n
    refine ⟨g, hReserved, hOld, ?_⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hImage)

/-- A finite initial set of possible preimage INDICES t
is enough to obtain a finite cover of target leaf images F(t).
No increasing/order-preserving assumption on F is used. -/
theorem finiteHorizonNextLeafCover_of_bounded_preimage_index
    (H K : Ordered3Graph Nat) (F : Nat → Nat)
    (m : Nat) (f : Nat → Nat)
    (hBound : ∃ B : Nat, ∀ n : Nat, ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1 + n) g ∧
      CofinalDiaryStageCompatible H m f g ∧
      ∃ t : Nat, t < B ∧ g m = F t) :
    FiniteHorizonNextLeafCover H K F m f := by
  classical
  obtain ⟨B, hAll⟩ := hBound
  refine ⟨(Finset.range B).image F, ?_⟩
  intro n
  obtain ⟨g, hReserved, hOld, t, ht, hImage⟩ := hAll n
  refine ⟨g, hReserved, hOld, ?_⟩
  exact Finset.mem_image.mpr
    ⟨t, Finset.mem_range.mpr ht, hImage.symm⟩

end DiaryLeafPriority
end ThreeUniformDiaries
