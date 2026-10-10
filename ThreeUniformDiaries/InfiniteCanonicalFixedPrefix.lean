import ThreeUniformDiaries.InfiniteCanonicalSelectedAuxBits
import ThreeUniformDiaries.InfiniteCanonicalSelectedPairs
import ThreeUniformDiaries.InfiniteCanonicalSelectedTriples

/-!
# Exact fixed initial levels for actual infinite canonical coordinate maps

In the manuscript's anchored strong vector subtrees, f(j)=j for j<n.
The genuine recursively constructed infinite E2/E1/E0 maps then fix
LITERALLY every source node of every coordinate type at every level
N<n, not merely the selected edge bits.

The proofs use already checked all-selected-bit preservation, along
with the zero-outside-support laws. They do not assume the full
CanonicalMap record or an extra geometric fixed-prefix axiom.
This is the fixed-initial-segment component of the geometric
canonical composition lemma.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteAuxCanonicalMap_fixed_prefix
    {S : Set CoordNode} {f : Nat → Nat}
    {r : AuxNode (f 0)}
    (hS : InfiniteStrongPicture S f (.aux (f 0) r))
    (hf : StrictMono f)
    {n : Nat} (hfix : ∀ i < n, f i = i)
    (N : Nat) (hN : N < n) (a : AuxNode N) :
    CoordNode.aux (f N) (infiniteAuxCanonicalMap hS N a).val =
      CoordNode.aux N a := by
  have hFN : f N = N := hfix N hN
  rw [hFN]
  apply congrArg (CoordNode.aux N)
  apply AuxNode.ext_bits
  funext i
  by_cases hi : i < N
  · have hfi : f i = i := hfix i (lt_trans hi hN)
    have hb := infiniteAuxCanonicalMap_selectedBit hS hf N i hi a
    simpa [hfi] using hb
  · rw [(infiniteAuxCanonicalMap hS N a).val.support i (by omega),
        a.support i (by omega)]

theorem infiniteOneCanonicalMap_fixed_prefix
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    {n : Nat} (hfix : ∀ i < n, f i = i)
    (N : Nat) (hN : N < n) (a : OneNode N) :
    CoordNode.one (f N) (infiniteOneCanonicalMap h₁ h₂ N a).val =
      CoordNode.one N a := by
  have hFN : f N = N := hfix N hN
  rw [hFN]
  apply congrArg (CoordNode.one N)
  apply OneNode.ext_pairs
  funext i j
  by_cases hvalid : i < j ∧ j < N
  · have hfi : f i = i := hfix i (by omega)
    have hfj : f j = j := hfix j (by omega)
    have hb := infiniteOneCanonicalMap_selectedPair
      h₁ h₂ hf N i j hvalid.1 hvalid.2 a
    simpa [hfi, hfj] using hb
  · rw [(infiniteOneCanonicalMap h₁ h₂ N a).val.support i j (by simpa [hFN] using hvalid),
        a.support i j hvalid]

theorem infiniteEnumCanonicalMap_fixed_prefix
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    {n : Nat} (hfix : ∀ i < n, f i = i)
    (N : Nat) (hN : N < n) (a : EnumNode N) :
    CoordNode.enum (f N) (infiniteEnumCanonicalMap h₀ h₁ h₂ N a).val =
      CoordNode.enum N a := by
  have hFN : f N = N := hfix N hN
  rw [hFN]
  apply congrArg (CoordNode.enum N)
  apply EnumNode.ext_triples
  funext i j k
  by_cases hvalid : i < j ∧ j < k ∧ k < N
  · have hfi : f i = i := hfix i (by omega)
    have hfj : f j = j := hfix j (by omega)
    have hfk : f k = k := hfix k (by omega)
    have hb := infiniteEnumCanonicalMap_selectedTriple
      h₀ h₁ h₂ hf N i j k hvalid.1 hvalid.2.1 hvalid.2.2 a
    simpa [hfi, hfj, hfk] using hb
  · rw [(infiniteEnumCanonicalMap h₀ h₁ h₂ N a).val.support i j k (by simpa [hFN] using hvalid),
        a.support i j k hvalid]

end CoordNode
end ThreeUniformDiaries
