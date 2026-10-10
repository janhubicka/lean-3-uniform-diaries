import ThreeUniformDiaries.InfiniteCanonicalSelectedTriples

/-!
# Injectivity of the actual infinite canonical maps

The manuscript's abstract CanonicalMap record assumes injectivity
in each coordinate. The recursively constructed infinite geometric
canonical maps instead DERIVE injectivity from the checked exact
preservation of all selected auxiliary, singleton and enumeration
bits. Bits off the source support vanish on both sides.

Thus these are direct geometric results for actual infinite strong
pictures and form the injectivity component of the missing concrete
CanonicalMap interface, without adding assumptions.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteAuxCanonicalMap_injective
    {S : Set CoordNode} {f : Nat → Nat}
    {r : AuxNode (f 0)}
    (hS : InfiniteStrongPicture S f (.aux (f 0) r))
    (hf : StrictMono f) (N : Nat) :
    Function.Injective
      (fun a : AuxNode N => (infiniteAuxCanonicalMap hS N a).val) := by
  intro a b hab
  change (infiniteAuxCanonicalMap hS N a).val =
    (infiniteAuxCanonicalMap hS N b).val at hab
  apply AuxNode.ext_bits
  funext i
  by_cases hi : i < N
  · calc
      a.bit i = (infiniteAuxCanonicalMap hS N a).val.bit (f i) :=
        (infiniteAuxCanonicalMap_selectedBit hS hf N i hi a).symm
      _ = (infiniteAuxCanonicalMap hS N b).val.bit (f i) := by
        rw [hab]
      _ = b.bit i :=
        infiniteAuxCanonicalMap_selectedBit hS hf N i hi b
  · rw [a.support i (by omega), b.support i (by omega)]

theorem infiniteOneCanonicalMap_injective
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f) (N : Nat) :
    Function.Injective
      (fun a : OneNode N => (infiniteOneCanonicalMap h₁ h₂ N a).val) := by
  intro a b hab
  change (infiniteOneCanonicalMap h₁ h₂ N a).val =
    (infiniteOneCanonicalMap h₁ h₂ N b).val at hab
  apply OneNode.ext_pairs
  funext i j
  by_cases h : i < j ∧ j < N
  · rcases h with ⟨hij, hjN⟩
    calc
      a.pair i j =
          (infiniteOneCanonicalMap h₁ h₂ N a).val.pair (f i) (f j) :=
        (infiniteOneCanonicalMap_selectedPair h₁ h₂ hf N i j hij hjN a).symm
      _ = (infiniteOneCanonicalMap h₁ h₂ N b).val.pair (f i) (f j) := by
        rw [hab]
      _ = b.pair i j :=
        infiniteOneCanonicalMap_selectedPair h₁ h₂ hf N i j hij hjN b
  · rw [a.support i j h, b.support i j h]

theorem infiniteEnumCanonicalMap_injective
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f) (N : Nat) :
    Function.Injective
      (fun a : EnumNode N => (infiniteEnumCanonicalMap h₀ h₁ h₂ N a).val) := by
  intro a b hab
  change (infiniteEnumCanonicalMap h₀ h₁ h₂ N a).val =
    (infiniteEnumCanonicalMap h₀ h₁ h₂ N b).val at hab
  apply EnumNode.ext_triples
  funext i j k
  by_cases h : i < j ∧ j < k ∧ k < N
  · rcases h with ⟨hij, hjk, hkN⟩
    calc
      a.triple i j k =
          (infiniteEnumCanonicalMap h₀ h₁ h₂ N a).val.triple
            (f i) (f j) (f k) :=
        (infiniteEnumCanonicalMap_selectedTriple
          h₀ h₁ h₂ hf N i j k hij hjk hkN a).symm
      _ = (infiniteEnumCanonicalMap h₀ h₁ h₂ N b).val.triple
            (f i) (f j) (f k) := by rw [hab]
      _ = b.triple i j k :=
        infiniteEnumCanonicalMap_selectedTriple
          h₀ h₁ h₂ hf N i j k hij hjk hkN b
  · rw [a.support i j k h, b.support i j k h]

end CoordNode
end ThreeUniformDiaries
