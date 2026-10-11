import ThreeUniformDiaries.InfiniteCanonicalFixedPrefix

/-!
# Fixed selected levels force complete initial coordinate layers

A genuine strong picture with selected levels f need not contain
every ambient node at arbitrary selected levels. However if
f(j)=j for every j<n, then the recursively constructed canonical
map is literally the identity on every source node on those levels.

Each canonical image belongs to its given strong picture. Hence,
without ANY separate fullness assumption, the entire ambient
initial prefix of every coordinate sort belongs to that picture.

This is the direct rooted/anchored condition needed to turn
geometric composition at level map f∘sigma into a member of Str_{n,omega}.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteAuxStrongPicture_completePrefix
    {S : Set CoordNode} {f : Nat → Nat}
    {r : AuxNode (f 0)}
    (hS : InfiniteStrongPicture S f (.aux (f 0) r))
    (hf : StrictMono f)
    {n : Nat} (hfix : ∀ i < n, f i = i) :
    ∀ i : Nat, i < n → ∀ a : AuxNode i,
      CoordNode.aux i a ∈ S := by
  intro i hi a
  have hmem := (infiniteAuxCanonicalMap hS i a).property
  have heq := infiniteAuxCanonicalMap_fixed_prefix hS hf hfix i hi a
  rw [heq] at hmem
  exact hmem

theorem infiniteOneStrongPicture_completePrefix
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    {n : Nat} (hfix : ∀ i < n, f i = i) :
    ∀ i : Nat, i < n → ∀ a : OneNode i,
      CoordNode.one i a ∈ S₁ := by
  intro i hi a
  have hmem := (infiniteOneCanonicalMap h₁ h₂ i a).property
  have heq := infiniteOneCanonicalMap_fixed_prefix h₁ h₂ hf hfix i hi a
  rw [heq] at hmem
  exact hmem

theorem infiniteEnumStrongPicture_completePrefix
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    {n : Nat} (hfix : ∀ i < n, f i = i) :
    ∀ i : Nat, i < n → ∀ a : EnumNode i,
      CoordNode.enum i a ∈ S₀ := by
  intro i hi a
  have hmem := (infiniteEnumCanonicalMap h₀ h₁ h₂ i a).property
  have heq := infiniteEnumCanonicalMap_fixed_prefix
    h₀ h₁ h₂ hf hfix i hi a
  rw [heq] at hmem
  exact hmem

end CoordNode
end ThreeUniformDiaries
