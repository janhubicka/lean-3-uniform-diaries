import ThreeUniformDiaries.FiniteCanonicalEnumRestriction

/-!
# Concrete finite canonical enumeration maps preserve ancestor order

The manuscript composition argument uses that canonical maps are
actual embeddings of the coordinate trees, not merely arbitrary
functions on each selected level.

The checked E0 truncation identity immediately gives preservation of
ancestor order: if A is the source initial segment of B, their
actual recursively constructed canonical images have precisely the
corresponding selected ancestor relation. This works across skipped
ambient levels and with an initial selected root above level zero.

This is a first geometric input to the meet-preservation and
composition lemmas; it does not assert either of those stronger
properties without a separate proof.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem finiteEnumCanonicalMap_preserves_prefix
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : FiniteStrongPicture S₀ f k (.enum (f 0) r₀))
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (hf : StrictMono f)
    (i j : Nat) (hij : i ≤ j) (hjk : j ≤ k)
    (A : EnumNode i) (B : EnumNode j)
    (hAB : B.truncate i = A) :
    CoordNode.enum (f i)
      (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i
        (by omega) A).val ≤
    CoordNode.enum (f j)
      (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ j
        hjk B).val := by
  have htrunc :=
    finiteEnumCanonicalMap_truncate h₀ h₁ h₂ hf i j hij hjk B
  rw [hAB] at htrunc
  refine ⟨hf.monotone hij, ?_⟩
  change CoordNode.enum (f i)
      ((finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ j
        hjk B).val.truncate (f i)) =
    CoordNode.enum (f i)
      (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i
        (by omega) A).val
  exact congrArg (CoordNode.enum (f i)) htrunc

end CoordNode
end ThreeUniformDiaries
