import ThreeUniformDiaries.FiniteStrongPrefixRigidity
import ThreeUniformDiaries.FiniteInfiniteBranchCoherence
import ThreeUniformDiaries.FiniteStrongInfiniteExtension

/-!
# Every genuine finite ATR F_I branch map has an infinite geometric realizer

The key next application step is not merely to extend a finite E0/E1/E2
strong picture to infinite height, but to show the finite *canonical
branch action* is exactly the restriction of the independently
constructed infinite canonical map, at every source branch vertex
whose last index lies in the finite height.

The proof combines three already checked theorems: infinite extension
of finite strong pictures, rigidity of their selected prefixes inside
those extensions, and finite/infinite canonical-map coherence.
This explicitly removes any assumed finite-to-infinite F_I compatibility
field from the eventual scalar realization interface.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- For arbitrary genuine infinite strong extensions of a synchronized
finite vector, the literal F_I branch images have the same last index
and the same target enumeration at every finite source index. -/
theorem finiteStrong_extension_branchMap_fields
    {S₀ S₁ S₂ U₀ U₁ U₂ : Set CoordNode}
    {f : Nat → Nat} {k : Nat}
    {r₀ : EnumNode (f 0)}
    {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (hS₀ : FiniteStrongPicture S₀ f k (.enum (f 0) r₀))
    (hS₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (hS₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (hU₀ : InfiniteStrongPicture U₀ f (.enum (f 0) r₀))
    (hU₁ : InfiniteStrongPicture U₁ f (.one (f 0) r₁))
    (hU₂ : InfiniteStrongPicture U₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    (hSU₀ : S₀ ⊆ U₀) (hSU₁ : S₁ ⊆ U₁) (hSU₂ : S₂ ⊆ U₂)
    (B : EnumerationBranchNode) (hB : B.last ≤ k) :
    (finiteStrongPicture_branchMap hS₀ hS₁ hS₂ B hB).enumeration =
      ((infiniteStrongPictureCanonicalMap hU₀ hU₁ hU₂ hf).mapBranch B).enumeration ∧
    (finiteStrongPicture_branchMap hS₀ hS₁ hS₂ B hB).last =
      ((infiniteStrongPictureCanonicalMap hU₀ hU₁ hU₂ hf).mapBranch B).last := by
  have hEq₀ : S₀ = infiniteStrongPicture_finitePrefix U₀ f k :=
    finiteStrongPicture_eq_infinitePrefix_of_subset
      hS₀ hU₀ hf rfl hSU₀
  have hEq₁ : S₁ = infiniteStrongPicture_finitePrefix U₁ f k :=
    finiteStrongPicture_eq_infinitePrefix_of_subset
      hS₁ hU₁ hf rfl hSU₁
  have hEq₂ : S₂ = infiniteStrongPicture_finitePrefix U₂ f k :=
    finiteStrongPicture_eq_infinitePrefix_of_subset
      hS₂ hU₂ hf rfl hSU₂
  subst S₀
  subst S₁
  subst S₂
  exact ⟨finitePrefix_branchMap_enumeration_eq_infinite
      hU₀ hU₁ hU₂ hf k B hB,
    finitePrefix_branchMap_last_eq_infinite
      hU₀ hU₁ hU₂ hf k B hB⟩

/-- Every genuine finite strong vector has synchronized infinite strong
extensions such that their canonical F_I action agrees with the
original finite action on ALL enumeration branch vertices of height
at most k, not just the distinguished g_A image. -/
theorem exists_infinite_extension_with_branchMap_fields
    {S₀ S₁ S₂ : Set CoordNode}
    {f : Nat → Nat} {k : Nat}
    {r₀ : EnumNode (f 0)}
    {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (hS₀ : FiniteStrongPicture S₀ f k (.enum (f 0) r₀))
    (hS₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (hS₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (hf : StrictMono f) :
    ∃ (U₀ U₁ U₂ : Set CoordNode),
      ∃ (hU₀ : InfiniteStrongPicture U₀ f (.enum (f 0) r₀))
        (hU₁ : InfiniteStrongPicture U₁ f (.one (f 0) r₁))
        (hU₂ : InfiniteStrongPicture U₂ f (.aux (f 0) r₂)),
        S₀ ⊆ U₀ ∧ S₁ ⊆ U₁ ∧ S₂ ⊆ U₂ ∧
        ∀ B : EnumerationBranchNode, ∀ hB : B.last ≤ k,
          (finiteStrongPicture_branchMap hS₀ hS₁ hS₂ B hB).enumeration =
            ((infiniteStrongPictureCanonicalMap hU₀ hU₁ hU₂ hf).mapBranch B).enumeration ∧
          (finiteStrongPicture_branchMap hS₀ hS₁ hS₂ B hB).last =
            ((infiniteStrongPictureCanonicalMap hU₀ hU₁ hU₂ hf).mapBranch B).last := by
  obtain ⟨U₀, hSU₀, hU₀⟩ :=
    finiteStrongPicture_exists_infinite_extension hS₀ hf
  obtain ⟨U₁, hSU₁, hU₁⟩ :=
    finiteStrongPicture_exists_infinite_extension hS₁ hf
  obtain ⟨U₂, hSU₂, hU₂⟩ :=
    finiteStrongPicture_exists_infinite_extension hS₂ hf
  refine ⟨U₀, U₁, U₂, hU₀, hU₁, hU₂,
    hSU₀, hSU₁, hSU₂, ?_⟩
  intro B hB
  exact finiteStrong_extension_branchMap_fields
    hS₀ hS₁ hS₂ hU₀ hU₁ hU₂ hf
    hSU₀ hSU₁ hSU₂ B hB

end CoordNode
end ThreeUniformDiaries
