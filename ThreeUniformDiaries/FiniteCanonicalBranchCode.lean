import ThreeUniformDiaries.FiniteCoupledCanonicalMaps
import ThreeUniformDiaries.FiniteSelectedSuccessorBridge

/-!
# The last algebraic step in the finite Aemb coding identity

Once the concrete recursively constructed E0 and E1 coordinate maps
take the source enumeration and one-type at cut i to their prescribed
target nodes at f(i), the F_I^S code of the source prefix ending at i
is *literally* the target enumeration prefix ending at f(i).

The proof is independent of the global Ramsey/Milliken transfer and
works with the actual finite-height map constructors, not the abstract
all-level CanonicalMap structure. The remaining Aemb obligations are
precisely the candidate-image identities and their roots.
-/

namespace ThreeUniformDiaries
namespace EnumNode

theorem finiteCanonical_branch_code_of_coordinates
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : CoordNode.FiniteStrongPicture S₀ f k
      (.enum (f 0) r₀))
    (h₁ : CoordNode.FiniteStrongPicture S₁ f k
      (.one (f 0) r₁))
    (h₂ : CoordNode.FiniteStrongPicture S₂ f k
      (.aux (f 0) r₂))
    (i : Nat) (hi : i ≤ k)
    (hEnum :
      (CoordNode.finiteStrongPicture_enumCanonicalMap
        h₀ h₁ h₂ i hi (A.truncate i)).val =
          H.truncate (f i))
    (hOne :
      (CoordNode.finiteStrongPicture_oneCanonicalMap
        h₁ h₂ i hi (A.oneType i i)).val =
          H.oneType (f i) (f i)) :
    (CoordNode.finiteStrongPicture_enumCanonicalMap
      h₀ h₁ h₂ i hi (A.truncate i)).val.succ
      (CoordNode.finiteStrongPicture_oneCanonicalMap
        h₁ h₂ i hi (A.oneType i i)).val =
      H.truncate (f i + 1) := by
  rw [hEnum, hOne]
  apply EnumNode.ext_triples
  funext a b c
  exact (H.truncate_succ_triple
    (l := f i) (i := a) (j := b) (k := c)).symm

end EnumNode
end ThreeUniformDiaries
