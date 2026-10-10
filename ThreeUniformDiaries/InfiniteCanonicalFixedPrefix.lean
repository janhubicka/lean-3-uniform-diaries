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
  have htyped :
      a.truncate (f N) = (infiniteAuxCanonicalMap hS N a).val := by
    apply AuxNode.ext_bits
    funext i
    by_cases hi : i < N
    · have hif : i < f N := by simpa only [hFN] using hi
      have hfi : f i = i := hfix i (lt_trans hi hN)
      have hb := infiniteAuxCanonicalMap_selectedBit hS hf N i hi a
      calc
        (a.truncate (f N)).bit i = a.bit i := by
          simp [AuxNode.truncate, hif]
        _ = (infiniteAuxCanonicalMap hS N a).val.bit i := by
          simpa only [hfi] using hb.symm
    · have hge : f N ≤ i := by omega
      exact ((a.truncate (f N)).support i hge).trans
        ((infiniteAuxCanonicalMap hS N a).val.support i hge).symm
  have hle :
      CoordNode.aux (f N) (infiniteAuxCanonicalMap hS N a).val ≤
        CoordNode.aux N a := by
    refine ⟨by simpa only [level, hFN], ?_⟩
    change CoordNode.aux (f N) (a.truncate (f N)) =
      CoordNode.aux (f N) (infiniteAuxCanonicalMap hS N a).val
    exact congrArg (CoordNode.aux (f N)) htyped
  exact eq_of_le_of_level_eq hle hFN

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
  have htyped :
      a.truncate (f N) = (infiniteOneCanonicalMap h₁ h₂ N a).val := by
    apply OneNode.ext_pairs
    funext i j
    by_cases hvalid : i < j ∧ j < N
    · have hfi : f i = i := hfix i (by omega)
      have hfj : f j = j := hfix j (by omega)
      have hjf : j < f N := by simpa only [hFN] using hvalid.2
      have hb := infiniteOneCanonicalMap_selectedPair
        h₁ h₂ hf N i j hvalid.1 hvalid.2 a
      calc
        (a.truncate (f N)).pair i j = a.pair i j := by
          simp [OneNode.truncate, hjf]
        _ = (infiniteOneCanonicalMap h₁ h₂ N a).val.pair i j := by
          simpa only [hfi, hfj] using hb.symm
    · have hbad : ¬ (i < j ∧ j < f N) := by
        simpa only [hFN] using hvalid
      exact ((a.truncate (f N)).support i j hbad).trans
        ((infiniteOneCanonicalMap h₁ h₂ N a).val.support i j hbad).symm
  have hle :
      CoordNode.one (f N) (infiniteOneCanonicalMap h₁ h₂ N a).val ≤
        CoordNode.one N a := by
    refine ⟨by simpa only [level, hFN], ?_⟩
    change CoordNode.one (f N) (a.truncate (f N)) =
      CoordNode.one (f N) (infiniteOneCanonicalMap h₁ h₂ N a).val
    exact congrArg (CoordNode.one (f N)) htyped
  exact eq_of_le_of_level_eq hle hFN

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
  have htyped :
      a.truncate (f N) = (infiniteEnumCanonicalMap h₀ h₁ h₂ N a).val := by
    apply EnumNode.ext_triples
    funext i j k
    by_cases hvalid : i < j ∧ j < k ∧ k < N
    · have hfi : f i = i := hfix i (by omega)
      have hfj : f j = j := hfix j (by omega)
      have hfk : f k = k := hfix k (by omega)
      have hkf : k < f N := by simpa only [hFN] using hvalid.2.2
      have hb := infiniteEnumCanonicalMap_selectedTriple
        h₀ h₁ h₂ hf N i j k hvalid.1 hvalid.2.1 hvalid.2.2 a
      calc
        (a.truncate (f N)).triple i j k = a.triple i j k := by
          simp [EnumNode.truncate, hkf]
        _ = (infiniteEnumCanonicalMap h₀ h₁ h₂ N a).val.triple i j k := by
          simpa only [hfi, hfj, hfk] using hb.symm
    · have hbad : ¬ (i < j ∧ j < k ∧ k < f N) := by
        simpa only [hFN] using hvalid
      exact ((a.truncate (f N)).support i j k hbad).trans
        ((infiniteEnumCanonicalMap h₀ h₁ h₂ N a).val.support i j k hbad).symm
  have hle :
      CoordNode.enum (f N) (infiniteEnumCanonicalMap h₀ h₁ h₂ N a).val ≤
        CoordNode.enum N a := by
    refine ⟨by simpa only [level, hFN], ?_⟩
    change CoordNode.enum (f N) (a.truncate (f N)) =
      CoordNode.enum (f N) (infiniteEnumCanonicalMap h₀ h₁ h₂ N a).val
    exact congrArg (CoordNode.enum (f N)) htyped
  exact eq_of_le_of_level_eq hle hFN

end CoordNode
end ThreeUniformDiaries
