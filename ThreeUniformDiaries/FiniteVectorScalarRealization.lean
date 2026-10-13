import ThreeUniformDiaries.RootGluedVectorRefinement
import ThreeUniformDiaries.FiniteStrongPrefixRigidity
import ThreeUniformDiaries.FiniteStrongInfiniteExtension

/-!
# Realize every genuine finite E0/E1/E2 strong vector as a scalar approximation

An arbitrary finite ATR code S is a synchronized triple of actual
finite strong pictures, not a hypothetical scalar subtree. The
manuscript's Milliken application needs an exact scalar finite
approximation a whose three coordinate slices are literally S.

Extend each finite picture to genuine infinite strong height on
the same selected map f; finite-prefix rigidity proves that the
original finite pictures are precisely the first k+1 source levels.
Root-glue the three infinite extensions and use the checked
finite-prefix correspondence in the actual Milliken StrongSubtree.

This is the finite vector-to-scalar REALIZATION direction, without
assuming a general Milliken theorem, a uniform branching degree,
or a synthetic FinCode→scalar approximation correspondence.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Every synchronized genuine finite strong vector picture has
an actual scalar Milliken strong-tree realizer whose finite
height-(k+2) approximation has precisely the three prescribed
coordinate carriers, with the exact shifted selected level map. -/
theorem exists_scalarApprox_of_finiteStrongVector
    {S₀ S₁ S₂ : Set CoordNode}
    {f : Nat → Nat} {k : Nat}
    {r₀ : EnumNode (f 0)}
    {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : FiniteStrongPicture S₀ f k (.enum (f 0) r₀))
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (hf : StrictMono f) :
    ∃ (T : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
      (F : TypedVectorSubset),
      T.levels = selectedGluedLevels f ∧
      F.carrier 0 = S₀ ∧
      F.carrier 1 = S₁ ∧
      F.carrier 2 = S₂ ∧
      (Milliken.GeneralTree.r (k + 2) T).carrier = F.glue := by
  obtain ⟨U₀, hS₀U, hU₀⟩ :=
    finiteStrongPicture_exists_infinite_extension h₀ hf
  obtain ⟨U₁, hS₁U, hU₁⟩ :=
    finiteStrongPicture_exists_infinite_extension h₁ hf
  obtain ⟨U₂, hS₂U, hU₂⟩ :=
    finiteStrongPicture_exists_infinite_extension h₂ hf
  let T := gluedVectorStrong_to_milliken hU₀ hU₁ hU₂ hf
  let F := (typedVectorOfStrong hU₀ hU₁ hU₂).truncateSelected f (k + 1)
  have hTlevels : T.levels = selectedGluedLevels f := by
    change gluedSelectedLevel f = selectedGluedLevels f
    exact gluedSelectedLevel_eq_selectedGluedLevels f
  obtain ⟨hF₀, hF₁, hF₂⟩ :=
    typedVectorStrong_finiteSlice_eq hU₀ hU₁ hU₂ hf k
  have hEq₀ : F.carrier 0 = S₀ := by
    exact hF₀.trans
      (finiteStrongPicture_eq_infinitePrefix_of_subset
        h₀ hU₀ hf rfl hS₀U).symm
  have hEq₁ : F.carrier 1 = S₁ := by
    exact hF₁.trans
      (finiteStrongPicture_eq_infinitePrefix_of_subset
        h₁ hU₁ hf rfl hS₁U).symm
  have hEq₂ : F.carrier 2 = S₂ := by
    exact hF₂.trans
      (finiteStrongPicture_eq_infinitePrefix_of_subset
        h₂ hU₂ hf rfl hS₂U).symm
  have hTpart :
      (Milliken.GeneralTree.r (k + 2) T).carrier = F.glue := by
    change T.initialPart (k + 2) = F.glue
    simpa only [T, F, Nat.add_assoc] using
      (gluedVectorStrong_initialPart_eq_vectorPrefix
        hU₀ hU₁ hU₂ hf (k + 1))
  exact ⟨T, F, hTlevels, hEq₀, hEq₁, hEq₂, hTpart⟩

end CoordNode
end ThreeUniformDiaries
