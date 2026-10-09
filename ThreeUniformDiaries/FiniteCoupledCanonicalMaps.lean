import ThreeUniformDiaries.FiniteStrongTypedOneEnumLift
import ThreeUniformDiaries.FiniteAuxCanonicalMap

/-!
# Genuine finite canonical maps for all three type-tree coordinates

The auxiliary coordinate map is already constructed in
FiniteAuxCanonicalMap. The remaining two coordinates now follow the
same selected-step recursion, with their successor parameters provided
by the previously constructed lower-coordinate maps:

  auxiliary bits -> singleton successor parameters -> enumeration parameters.

Thus these are actual maps induced by concrete finite strong pictures,
not fields of an abstract CanonicalMap structure. All mapped nodes are
proved to lie in the relevant completed strong picture, and the roots
are correct even when the first selected ambient level is nonzero.

The next separate obligation is exact identification of prescribed
Aemb candidate nodes, and then F_I^S ∘ g_A = g_H ∘ e.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Concrete finite singleton-type canonical map, using the already
constructed auxiliary coordinate map for each new boundary parameter. -/
noncomputable def finiteStrongPicture_oneCanonicalMap
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂)) :
    (i : Nat) → (hi : i ≤ k) → OneNode i →
      {b : OneNode (f i) // CoordNode.one (f i) b ∈ S₁}
  | 0, _, _ => ⟨r₁, h₁.2.2.1⟩
  | i + 1, hi, a => by
      have hik : i < k := by omega
      have hik0 : i ≤ k := by omega
      let prev :=
        finiteStrongPicture_oneCanonicalMap h₁ h₂ i hik0
          (a.truncate i)
      let param :=
        finiteStrongPicture_auxCanonicalMap h₂ i hik0
          (a.boundaryAux i)
      let b := finiteStrongPicture_oneStep h₁
        i hik prev.val prev.property param.val
      have hb :=
        (finiteStrongPicture_oneStep_spec h₁
          i hik prev.val prev.property param.val).1
      exact ⟨b, hb⟩

/-- Concrete finite enumeration canonical map, whose new parameter is
obtained from the previously constructed singleton coordinate map. -/
noncomputable def finiteStrongPicture_enumCanonicalMap
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : FiniteStrongPicture S₀ f k (.enum (f 0) r₀))
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂)) :
    (i : Nat) → (hi : i ≤ k) → EnumNode i →
      {b : EnumNode (f i) // CoordNode.enum (f i) b ∈ S₀}
  | 0, _, _ => ⟨r₀, h₀.2.2.1⟩
  | i + 1, hi, a => by
      have hik : i < k := by omega
      have hik0 : i ≤ k := by omega
      let prev :=
        finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i hik0
          (a.truncate i)
      let param :=
        finiteStrongPicture_oneCanonicalMap h₁ h₂ i hik0
          (a.boundaryOne i)
      let b := finiteStrongPicture_enumStep h₀
        i hik prev.val prev.property param.val
      have hb :=
        (finiteStrongPicture_enumStep_spec h₀
          i hik prev.val prev.property param.val).1
      exact ⟨b, hb⟩

@[simp] theorem finiteStrongPicture_oneCanonicalMap_root
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (a : OneNode 0) :
    (finiteStrongPicture_oneCanonicalMap h₁ h₂
      0 (Nat.zero_le k) a).val = r₁ := rfl

@[simp] theorem finiteStrongPicture_enumCanonicalMap_root
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : FiniteStrongPicture S₀ f k (.enum (f 0) r₀))
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (a : EnumNode 0) :
    (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂
      0 (Nat.zero_le k) a).val = r₀ := rfl

end CoordNode
end ThreeUniformDiaries
