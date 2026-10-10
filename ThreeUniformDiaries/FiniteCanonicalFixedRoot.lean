import ThreeUniformDiaries.FiniteCoupledCanonicalMaps

/-!
# First fixed level of the concrete finite canonical maps

If the first selected ambient level is 0 and the completed strong
picture retains the full ambient root level, the concrete map sends
the unique source root to that very root. This holds separately and
simultaneously in the auxiliary, singleton and enumeration trees.

These are the level-zero base cases for the required fixed-prefix
identity f_i^S|T_i(<n)=id when n>0. No abstract CanonicalMap fields
are assumed.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem finiteAuxCanonicalMap_fixed_root
    {S : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r : AuxNode (f 0)}
    (hS : FiniteStrongPicture S f k (.aux (f 0) r))
    (hzero : f 0 = 0)
    (hfull : ∀ a : AuxNode 0, CoordNode.aux 0 a ∈ S)
    (a : AuxNode 0) :
    CoordNode.aux (f 0)
      (finiteStrongPicture_auxCanonicalMap hS 0
        (Nat.zero_le k) a).val =
    CoordNode.aux 0 a := by
  change CoordNode.aux (f 0) r = CoordNode.aux 0 a
  have hbelow : CoordNode.aux (f 0) r ≤ .aux 0 a :=
    hS.2.2.2.1 _ (hfull a)
  apply eq_of_le_of_level_eq hbelow
  simp [hzero, level]

theorem finiteOneCanonicalMap_fixed_root
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (hzero : f 0 = 0)
    (hfull : ∀ a : OneNode 0, CoordNode.one 0 a ∈ S₁)
    (a : OneNode 0) :
    CoordNode.one (f 0)
      (finiteStrongPicture_oneCanonicalMap h₁ h₂ 0
        (Nat.zero_le k) a).val =
    CoordNode.one 0 a := by
  change CoordNode.one (f 0) r₁ = CoordNode.one 0 a
  have hbelow : CoordNode.one (f 0) r₁ ≤ .one 0 a :=
    h₁.2.2.2.1 _ (hfull a)
  apply eq_of_le_of_level_eq hbelow
  simp [hzero, level]

theorem finiteEnumCanonicalMap_fixed_root
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : FiniteStrongPicture S₀ f k (.enum (f 0) r₀))
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (hzero : f 0 = 0)
    (hfull : ∀ a : EnumNode 0, CoordNode.enum 0 a ∈ S₀)
    (a : EnumNode 0) :
    CoordNode.enum (f 0)
      (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ 0
        (Nat.zero_le k) a).val =
    CoordNode.enum 0 a := by
  change CoordNode.enum (f 0) r₀ = CoordNode.enum 0 a
  have hbelow : CoordNode.enum (f 0) r₀ ≤ .enum 0 a :=
    h₀.2.2.2.1 _ (hfull a)
  apply eq_of_le_of_level_eq hbelow
  simp [hzero, level]

end CoordNode
end ThreeUniformDiaries
