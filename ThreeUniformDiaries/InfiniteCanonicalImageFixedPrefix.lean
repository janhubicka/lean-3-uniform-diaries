import ThreeUniformDiaries.InfiniteCanonicalFixedPrefix
import ThreeUniformDiaries.InfiniteAuxMeetClosedImage
import ThreeUniformDiaries.InfiniteGeometricImageMeetClosed

/-!
# Protected initial levels survive literal geometric image completion

The manuscript needs the composite strong vector picture V to
contain ALL of the first n ambient type-tree levels, not merely
the three composite roots. This condition is independent of
the composition equality itself.

If the outer genuine geometric canonical maps fix those levels
and the inner source coordinate picture contains them all, their
actual images contain those nodes literally. Every completion of
the images therefore also contains them.

The proofs work for each of the three coordinates, including n=0.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteAuxImage_completePrefix
    {U : Set CoordNode} {f : Nat → Nat}
    {rU : AuxNode (f 0)}
    (hU : InfiniteStrongPicture U f (.aux (f 0) rU))
    (hf : StrictMono f)
    {n : Nat} (hfix : ∀ i < n, f i = i)
    (E V : Set CoordNode)
    (hfull : ∀ i : Nat, i < n → ∀ a : AuxNode i,
      CoordNode.aux i a ∈ E)
    (hEV : infiniteAuxImage hU E ⊆ V) :
    ∀ i : Nat, i < n → ∀ a : AuxNode i,
      CoordNode.aux i a ∈ V := by
  intro i hi a
  apply hEV
  refine ⟨i, a, hfull i hi a, ?_⟩
  exact (infiniteAuxCanonicalMap_fixed_prefix hU hf hfix i hi a).symm

theorem infiniteOneImage_completePrefix
    {U₁ U₂ : Set CoordNode} {f : Nat → Nat}
    {rU₁ : OneNode (f 0)} {rU₂ : AuxNode (f 0)}
    (hU₁ : InfiniteStrongPicture U₁ f (.one (f 0) rU₁))
    (hU₂ : InfiniteStrongPicture U₂ f (.aux (f 0) rU₂))
    (hf : StrictMono f)
    {n : Nat} (hfix : ∀ i < n, f i = i)
    (E V : Set CoordNode)
    (hfull : ∀ i : Nat, i < n → ∀ a : OneNode i,
      CoordNode.one i a ∈ E)
    (hEV : infiniteOneImage hU₁ hU₂ E ⊆ V) :
    ∀ i : Nat, i < n → ∀ a : OneNode i,
      CoordNode.one i a ∈ V := by
  intro i hi a
  apply hEV
  refine ⟨i, a, hfull i hi a, ?_⟩
  exact (infiniteOneCanonicalMap_fixed_prefix
    hU₁ hU₂ hf hfix i hi a).symm

theorem infiniteEnumImage_completePrefix
    {U₀ U₁ U₂ : Set CoordNode} {f : Nat → Nat}
    {rU₀ : EnumNode (f 0)} {rU₁ : OneNode (f 0)}
    {rU₂ : AuxNode (f 0)}
    (hU₀ : InfiniteStrongPicture U₀ f (.enum (f 0) rU₀))
    (hU₁ : InfiniteStrongPicture U₁ f (.one (f 0) rU₁))
    (hU₂ : InfiniteStrongPicture U₂ f (.aux (f 0) rU₂))
    (hf : StrictMono f)
    {n : Nat} (hfix : ∀ i < n, f i = i)
    (E V : Set CoordNode)
    (hfull : ∀ i : Nat, i < n → ∀ a : EnumNode i,
      CoordNode.enum i a ∈ E)
    (hEV : infiniteEnumImage hU₀ hU₁ hU₂ E ⊆ V) :
    ∀ i : Nat, i < n → ∀ a : EnumNode i,
      CoordNode.enum i a ∈ V := by
  intro i hi a
  apply hEV
  refine ⟨i, a, hfull i hi a, ?_⟩
  exact (infiniteEnumCanonicalMap_fixed_prefix
    hU₀ hU₁ hU₂ hf hfix i hi a).symm

end CoordNode
end ThreeUniformDiaries
