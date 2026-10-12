import ThreeUniformDiaries.RootGluedActualFiniteApprox
import ThreeUniformDiaries.RootGluedGeneralStrong
import Milliken.GeneralTree.OrderLemmas

/-!
# Exact ATR vector/scalar refinement and finite-prefix correspondence

This module relates the *literal* E0/E1/E2 strong picture carriers to
inclusion of their actual root-glued Milliken strong subtrees.
Nothing here is an assumed vector/scalar equivalence or a substitute for
the unproved reverse strong-tree extraction.

The second theorem identifies the finite Milliken approximation with
the real three-coordinate selected prefix of those pictures, not just
with a level set of an abstract coded tree.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The two independently introduced shifted level-map definitions
are equal at every source level. -/
theorem gluedSelectedLevel_eq_selectedGluedLevels
    (f : Nat → Nat) :
    gluedSelectedLevel f = selectedGluedLevels f := by
  funext n
  cases n <;> rfl

/-- Root-gluing reflects and preserves *exactly* componentwise
subset inclusion for typed E0/E1/E2 carriers. -/
theorem typedVector_glue_subset_iff
    (V W : TypedVectorSubset) :
    V.glue ⊆ W.glue ↔
      ∀ i : Fin 3, V.carrier i ⊆ W.carrier i := by
  constructor
  · intro h i x hx
    have hs : sort x = i := V.correctlyTyped i x hx
    have hV : some x ∈ V.glue := by
      apply (V.some_mem_iff x).mpr
      change x ∈ V.carrier (sort x)
      simpa only [hs] using hx
    have hW : x ∈ W.carrier (sort x) :=
      (W.some_mem_iff x).mp (h hV)
    simpa only [hs] using hW
  · intro h x hx
    cases x with
    | none =>
        exact W.root_mem
    | some x =>
        have hxV : x ∈ V.carrier (sort x) :=
          (V.some_mem_iff x).mp hx
        apply (W.some_mem_iff x).mpr
        exact h (sort x) hxV

/-- Full genuine strong-subtree refinement is precisely inclusion of
each of the three actual coordinate pictures. -/
theorem gluedVectorStrong_refines_iff
    {S₀ S₁ S₂ U₀ U₁ U₂ : Set CoordNode}
    {f g : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    {q₀ : EnumNode (g 0)} {q₁ : OneNode (g 0)}
    {q₂ : AuxNode (g 0)}
    (hS₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (hS₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (hS₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    (hU₀ : InfiniteStrongPicture U₀ g (.enum (g 0) q₀))
    (hU₁ : InfiniteStrongPicture U₁ g (.one (g 0) q₁))
    (hU₂ : InfiniteStrongPicture U₂ g (.aux (g 0) q₂))
    (hg : StrictMono g) :
    (gluedVectorStrong_to_milliken hS₀ hS₁ hS₂ hf).Refines
      (gluedVectorStrong_to_milliken hU₀ hU₁ hU₂ hg) ↔
      (S₀ ⊆ U₀ ∧ S₁ ⊆ U₁ ∧ S₂ ⊆ U₂) := by
  let V := typedVectorOfStrong hS₀ hS₁ hS₂
  let W := typedVectorOfStrong hU₀ hU₁ hU₂
  have hsub : V.glue ⊆ W.glue ↔
      ∀ i : Fin 3, V.carrier i ⊆ W.carrier i :=
    typedVector_glue_subset_iff V W
  change V.glue ⊆ W.glue ↔ _
  rw [hsub]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa only [V, W, typedVectorOfStrong_enum] using h 0
    · simpa only [V, W, typedVectorOfStrong_one] using h 1
    · simpa only [V, W, typedVectorOfStrong_aux] using h 2
  · rintro ⟨h₀, h₁, h₂⟩ i
    fin_cases i
    · simpa [V, W, typedVectorOfStrong] using h₀
    · simpa [V, W, typedVectorOfStrong] using h₁
    · simpa [V, W, typedVectorOfStrong] using h₂

/-- A genuine synchronized vector strong picture has exactly the
expected first k vector levels inside its scalar Milliken finite
approximation of height k+1 (one extra level is the glued root). -/
theorem gluedVectorStrong_initialPart_eq_vectorPrefix
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f) (k : Nat) :
    (gluedVectorStrong_to_milliken h₀ h₁ h₂ hf).initialPart (k + 1) =
      ((typedVectorOfStrong h₀ h₁ h₂).truncateSelected f k).glue := by
  let B := gluedVectorStrong_to_milliken h₀ h₁ h₂ hf
  have hlev : B.levels = selectedGluedLevels f := by
    change gluedSelectedLevel f = selectedGluedLevels f
    exact gluedSelectedLevel_eq_selectedGluedLevels f
  have hpart :=
    millikenStrong_initialPart_eq_gluedTruncation B f hlev k
  have hV :
      TypedVectorSubset.ofGlued B.carrier =
        typedVectorOfStrong h₀ h₁ h₂ := by
    change TypedVectorSubset.ofGlued
        (typedVectorOfStrong h₀ h₁ h₂).glue =
          typedVectorOfStrong h₀ h₁ h₂
    exact TypedVectorSubset.ofGlued_glue _
  simpa only [B, hV] using hpart

end CoordNode
end ThreeUniformDiaries
