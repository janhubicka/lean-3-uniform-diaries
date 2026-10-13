import ThreeUniformDiaries.ScalarCanonicalFiniteLevels
import ThreeUniformDiaries.FiniteStrongLevelCongruence

/-!
# Canonical finite E0/E1/E2 pictures extracted from one scalar approximation

The finite scalar approximation already determines its three typed
carriers and each selected coordinate height independently of which
infinite strong tree realizes it. The old finite geometry API used
an arbitrary infinite tail for the level map.

We now use the canonical strictly increasing extension of precisely
those finite heights and transport the actual three finite strong
pictures to this map. The only root casts occur at the first selected
height and are justified by its proved equality; no hypothetical
finite picture is inserted into the decoder.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree
open ThreeUniformDiaries.CoordNode

private theorem enum_root_cast {n m : Nat} (h : n = m)
    (a : EnumNode n) :
    CoordNode.enum n a =
      CoordNode.enum m (Eq.mp (congrArg EnumNode h) a) := by
  cases h
  rfl

private theorem one_root_cast {n m : Nat} (h : n = m)
    (a : OneNode n) :
    CoordNode.one n a =
      CoordNode.one m (Eq.mp (congrArg OneNode h) a) := by
  cases h
  rfl

private theorem aux_root_cast {n m : Nat} (h : n = m)
    (a : AuxNode n) :
    CoordNode.aux n a =
      CoordNode.aux m (Eq.mp (congrArg AuxNode h) a) := by
  cases h
  rfl

/-- Every scalar finite approximation containing the real glued root
has genuine finite coordinate strong pictures parameterized by the
ONE canonical level map of that approximation. -/
theorem finiteCode_has_canonical_pictures
    (k : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (hroot : (none : WithBot CoordNode) ∈ a.carrier) :
    let g := canonicalFiniteLevelMap k a
    ∃ (r₀ : EnumNode (g 0))
      (r₁ : OneNode (g 0))
      (r₂ : AuxNode (g 0)),
        FiniteStrongPicture ((finiteTypedCarrier k a).carrier 0)
          g k (.enum (g 0) r₀) ∧
        FiniteStrongPicture ((finiteTypedCarrier k a).carrier 1)
          g k (.one (g 0) r₁) ∧
        FiniteStrongPicture ((finiteTypedCarrier k a).carrier 2)
          g k (.aux (g 0) r₂) := by
  obtain ⟨f, hf, hfinite, r₀, r₁, r₂, h₀, h₁, h₂⟩ :=
    finiteCode_has_genuine_pictures k a hroot
  let g := canonicalFiniteLevelMap k a
  have hfg : ∀ i : Nat, i ≤ k → f i = g i := by
    intro i hi
    have hfi := hfinite ⟨i, Nat.lt_succ_of_le hi⟩
    have hgi := canonicalFiniteLevelMap_inside k a i hi
    exact hfi.symm.trans hgi.symm
  have hg0 : f 0 = g 0 := hfg 0 (Nat.zero_le k)
  let q₀ : EnumNode (g 0) :=
    Eq.mp (congrArg EnumNode hg0) r₀
  let q₁ : OneNode (g 0) :=
    Eq.mp (congrArg OneNode hg0) r₁
  let q₂ : AuxNode (g 0) :=
    Eq.mp (congrArg AuxNode hg0) r₂
  have hr₀ : (CoordNode.enum (f 0) r₀) =
      CoordNode.enum (g 0) q₀ := by
    exact enum_root_cast hg0 r₀
  have hr₁ : (CoordNode.one (f 0) r₁) =
      CoordNode.one (g 0) q₁ := by
    exact one_root_cast hg0 r₁
  have hr₂ : (CoordNode.aux (f 0) r₂) =
      CoordNode.aux (g 0) q₂ := by
    exact aux_root_cast hg0 r₂
  have hG₀ :=
    finiteStrongPicture_congr_finite_levels h₀ hfg
  have hG₁ :=
    finiteStrongPicture_congr_finite_levels h₁ hfg
  have hG₂ :=
    finiteStrongPicture_congr_finite_levels h₂ hfg
  rw [hr₀] at hG₀
  rw [hr₁] at hG₁
  rw [hr₂] at hG₂
  exact ⟨q₀, q₁, q₂, hG₀, hG₁, hG₂⟩

/-- The canonical level map is an honest strictly increasing choice
for each rooted finite scalar approximation, not an arbitrary
continuation supplied as a hidden input by a decoder. -/
theorem finiteCode_canonical_strictMono
    (k : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2)) :
    StrictMono (canonicalFiniteLevelMap k a) :=
  canonicalFiniteLevelMap_strictMono k a

end ATRFiniteDecoder
end ThreeUniformDiaries
