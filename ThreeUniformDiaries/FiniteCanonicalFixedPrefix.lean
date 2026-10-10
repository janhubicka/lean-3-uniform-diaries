import ThreeUniformDiaries.FiniteCanonicalFixedStep

/-!
# Concrete finite canonical maps fix every level of the anchored prefix

Suppose a three-coordinate finite strong picture has selected levels
f(0),...,f(k), with f(j)=j whenever j<n. If its first coordinate
levels are complete, then the recursively CONSTRUCTED canonical maps
fix every type-tree node on every level j<n, in all three coordinates.

The proof is triangular: at each selected level the auxiliary map is
fixed first, then singleton types using its auxiliary boundary
parameter, then enumerations using their singleton boundary
parameter. It invokes only the checked no-gap successor lemmas.

The result is the pointwise fixed-prefix fact needed to certify the
finite map F_I^S preserves the initial enumeration on all relative
K_I vertices, not only the chosen source branch.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem finiteCanonicalMaps_fixedPrefix
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {k n : Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : FiniteStrongPicture S₀ f k (.enum (f 0) r₀))
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (hfix : ∀ j < n, f j = j)
    (hn : n ≤ k + 1)
    (hfull₀ : ∀ a : EnumNode 0, CoordNode.enum 0 a ∈ S₀)
    (hfull₁ : ∀ a : OneNode 0, CoordNode.one 0 a ∈ S₁)
    (hfull₂ : ∀ a : AuxNode 0, CoordNode.aux 0 a ∈ S₂) :
    (∀ (i : Nat) (hi : i < n) (a : AuxNode i),
      CoordNode.aux (f i)
        (finiteStrongPicture_auxCanonicalMap h₂ i
          (by omega) a).val = CoordNode.aux i a) ∧
    (∀ (i : Nat) (hi : i < n) (a : OneNode i),
      CoordNode.one (f i)
        (finiteStrongPicture_oneCanonicalMap h₁ h₂ i
          (by omega) a).val = CoordNode.one i a) ∧
    (∀ (i : Nat) (hi : i < n) (a : EnumNode i),
      CoordNode.enum (f i)
        (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i
          (by omega) a).val = CoordNode.enum i a) := by
  have hall :
      ∀ (i : Nat) (hi : i < n) (hik : i ≤ k),
        (∀ a : AuxNode i,
          CoordNode.aux (f i)
            (finiteStrongPicture_auxCanonicalMap h₂ i hik a).val =
            CoordNode.aux i a) ∧
        (∀ a : OneNode i,
          CoordNode.one (f i)
            (finiteStrongPicture_oneCanonicalMap h₁ h₂ i hik a).val =
            CoordNode.one i a) ∧
        (∀ a : EnumNode i,
          CoordNode.enum (f i)
            (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i hik a).val =
            CoordNode.enum i a) := by
    intro i
    induction i with
    | zero =>
        intro hi hik
        have h0 : f 0 = 0 := hfix 0 hi
        exact ⟨
          finiteAuxCanonicalMap_fixed_root h₂ h0 hfull₂,
          finiteOneCanonicalMap_fixed_root h₁ h₂ h0 hfull₁,
          finiteEnumCanonicalMap_fixed_root h₀ h₁ h₂ h0 hfull₀⟩
    | succ j ih =>
        intro hi hik
        have hjn : j < n := by omega
        have hjk : j ≤ k := by omega
        have hjlt : j < k := by omega
        have hj : f j = j := hfix j hjn
        have hj1 : f (j + 1) = j + 1 := hfix (j + 1) hi
        obtain ⟨haux, hone, henum⟩ := ih hjn hjk
        refine ⟨?_, ?_, ?_⟩
        · intro a
          exact finiteAuxCanonicalMap_fixed_step h₂ j hjlt hj hj1
            a (haux (a.truncate j))
        · intro a
          exact finiteOneCanonicalMap_fixed_step h₁ h₂ j hjlt hj hj1
            a (hone (a.truncate j)) (haux (a.boundaryAux j))
        · intro a
          exact finiteEnumCanonicalMap_fixed_step
            h₀ h₁ h₂ j hjlt hj hj1
            a (henum (a.truncate j)) (hone (a.boundaryOne j))
  refine ⟨?_, ?_, ?_⟩
  · intro i hi a
    exact (hall i hi (by omega)).1 a
  · intro i hi a
    exact (hall i hi (by omega)).2.1 a
  · intro i hi a
    exact (hall i hi (by omega)).2.2 a

end CoordNode
end ThreeUniformDiaries
