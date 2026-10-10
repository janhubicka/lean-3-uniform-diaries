import ThreeUniformDiaries.FiniteCanonicalEnumRestriction
import ThreeUniformDiaries.FiniteCanonicalFixedPrefix

/-!
# The concrete enumeration map preserves the prescribed initial cut

For n>0, a finite canonical enumeration map which fixes every selected
level below n and has complete initial coordinate levels sends any
source enumeration at height j>=n to a target enumeration whose first
n vertices are EXACTLY the source first n vertices. The next selected
level f(n) may be strictly larger than n.

At the boundary n-1 to n, fixed predecessor and singleton-parameter
images force the target successor cone above the literal source
n-prefix. The selected-truncation theorem propagates this prefix
through all later selected levels.

No abstract CanonicalMap compatibility field is used.
-/

namespace ThreeUniformDiaries
namespace CoordNode

private def anchoredEnumSucc (x y : CoordNode) : CoordNode :=
  match x, y with
  | .enum i a, .one j b =>
      if h : i = j then .enum (i + 1) (a.succ (h.symm ▸ b))
      else zeroChild x
  | _, _ => zeroChild x

theorem finiteEnumCanonicalMap_preserves_initial_cut
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {k n : Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : FiniteStrongPicture S₀ f k (.enum (f 0) r₀))
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (hf : StrictMono f)
    (hfix : ∀ i < n, f i = i)
    (hn : n ≤ k)
    (hfull₀ : ∀ a : EnumNode 0, CoordNode.enum 0 a ∈ S₀)
    (hfull₁ : ∀ a : OneNode 0, CoordNode.one 0 a ∈ S₁)
    (hfull₂ : ∀ a : AuxNode 0, CoordNode.aux 0 a ∈ S₂)
    (j : Nat) (hnj : n ≤ j) (hjk : j ≤ k)
    (a : EnumNode j) :
    (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ j hjk a).val.truncate n =
      a.truncate n := by
  cases n with
  | zero =>
      apply EnumNode.ext_triples
      funext x y z
      have hbad : ¬ (x < y ∧ y < z ∧ z < 0) := by omega
      simp [EnumNode.truncate,
        (a.truncate 0).support x y z hbad]
  | succ i =>
      have hin : i < i + 1 := Nat.lt_succ_self i
      have hik : i < k := by omega
      have hfi : f i = i := hfix i hin
      let b : EnumNode (i + 1) := a.truncate (i + 1)
      obtain ⟨_, hone, henum⟩ :=
        finiteCanonicalMaps_fixedPrefix h₀ h₁ h₂
          hfix (by omega) hfull₀ hfull₁ hfull₂
      have hprev := henum i hin (b.truncate i)
      have hparam := hone i hin (b.boundaryOne i)
      have hcone := finiteStrongPicture_enumCanonicalMap_succ
        h₀ h₁ h₂ i hik (b.truncate i) (b.boundaryOne i)
      rw [EnumNode.succ_truncate_boundary] at hcone
      have hsucc :
          CoordNode.enum (f i + 1)
            ((finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i
              (Nat.le_of_lt hik) (b.truncate i)).val.succ
            (finiteStrongPicture_oneCanonicalMap h₁ h₂ i
              (Nat.le_of_lt hik) (b.boundaryOne i)).val) =
          CoordNode.enum (i + 1) b := by
        have hc := congrArg₂ anchoredEnumSucc hprev hparam
        simpa [anchoredEnumSucc, EnumNode.succ_truncate_boundary] using hc
      rw [hsucc] at hcone
      have hb :
          (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ (i + 1)
            (by omega) b).val.truncate (i + 1) = b := by
        have heq := hcone.2
        change CoordNode.enum (i + 1)
          ((finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ (i + 1)
            (by omega) b).val.truncate (i + 1)) =
          CoordNode.enum (i + 1) b at heq
        injection heq with hresult
      have hlevel : i + 1 ≤ f (i + 1) := by
        have hmono := hf (Nat.lt_succ_self i)
        omega
      have htrunc :=
        finiteEnumCanonicalMap_truncate h₀ h₁ h₂ hf
          (i + 1) j hnj hjk a
      calc
        (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ j hjk a).val
            .truncate (i + 1) =
          ((finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ j hjk a).val
            .truncate (f (i + 1))).truncate (i + 1) := by
              symm
              exact EnumNode.truncate_truncate _ hlevel
        _ = (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂
              (i + 1) (by omega) b).val.truncate (i + 1) := by
                rw [htrunc]
        _ = b := hb
        _ = a.truncate (i + 1) := rfl

end CoordNode
end ThreeUniformDiaries
