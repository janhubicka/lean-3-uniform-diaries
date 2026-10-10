import ThreeUniformDiaries.InfiniteCanonicalSuccessor

/-!
# Actual infinite enumeration canonical maps commute with restriction

The infinitely tall canonical E0 map is constructed recursively from
a genuine infinite strong picture, not from the compatibility fields
of an abstract CanonicalMap record. Its image of a source enumeration
at level j has, at every earlier selected target level f(i), exactly
the canonical image of its source predecessor at level i.

This holds for arbitrary skipped ambient levels and a nonzero first
selected root; it is the infinite-height analogue of the already
verified finite concrete selected-truncation theorem.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteEnumCanonicalMap_parent
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (j : Nat) (a : EnumNode (j + 1)) :
    (infiniteEnumCanonicalMap h₀ h₁ h₂ (j + 1) a).val.truncate (f j) =
    (infiniteEnumCanonicalMap h₀ h₁ h₂ j (a.truncate j)).val := by
  let p := infiniteEnumCanonicalMap h₀ h₁ h₂ j (a.truncate j)
  let c := infiniteOneCanonicalMap h₁ h₂ j (a.boundaryOne j)
  have hcone := infiniteEnumCanonicalMap_succ
    h₀ h₁ h₂ j (a.truncate j) (a.boundaryOne j)
  rw [EnumNode.succ_truncate_boundary] at hcone
  have hparent :
      CoordNode.enum (f j) p.val ≤
        CoordNode.enum (f j + 1) (p.val.succ c.val) := by
    refine ⟨Nat.le_succ _, ?_⟩
    change CoordNode.enum (f j)
      ((p.val.succ c.val).truncate (f j)) =
        CoordNode.enum (f j) p.val
    rw [EnumNode.truncate_succ]
  have htree :
      CoordNode.enum (f j) p.val ≤
        CoordNode.enum (f (j + 1))
          (infiniteEnumCanonicalMap h₀ h₁ h₂ (j + 1) a).val :=
    CoordNode.le_trans hparent hcone
  have heq := htree.2
  change CoordNode.enum (f j)
      ((infiniteEnumCanonicalMap h₀ h₁ h₂ (j + 1) a).val.truncate
        (f j)) =
    CoordNode.enum (f j) p.val at heq
  injection heq with hb

theorem infiniteEnumCanonicalMap_truncate
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    (i j : Nat) (hij : i ≤ j) (a : EnumNode j) :
    (infiniteEnumCanonicalMap h₀ h₁ h₂ j a).val.truncate (f i) =
      (infiniteEnumCanonicalMap h₀ h₁ h₂ i (a.truncate i)).val := by
  have hmain :
      ∀ (j : Nat) (i : Nat) (hij : i ≤ j) (a : EnumNode j),
      (infiniteEnumCanonicalMap h₀ h₁ h₂ j a).val.truncate (f i) =
        (infiniteEnumCanonicalMap h₀ h₁ h₂ i (a.truncate i)).val := by
    intro j
    induction j with
    | zero =>
        intro i hij a
        have hi : i = 0 := by omega
        subst i
        simp only [EnumNode.truncate_self]
    | succ j ih =>
        intro i hij a
        by_cases heq : i = j + 1
        · subst i
          simp only [EnumNode.truncate_self]
        · have hij0 : i ≤ j := by omega
          have hparent :=
            infiniteEnumCanonicalMap_parent h₀ h₁ h₂ j a
          have hprev := ih i hij0 (a.truncate j)
          have hlevels : f i ≤ f j := hf.monotone hij0
          calc
            (infiniteEnumCanonicalMap h₀ h₁ h₂ (j + 1) a).val.truncate (f i) =
              ((infiniteEnumCanonicalMap h₀ h₁ h₂ (j + 1) a).val.truncate (f j)).truncate (f i) := by
                  symm
                  exact EnumNode.truncate_truncate _ hlevels
            _ = (infiniteEnumCanonicalMap h₀ h₁ h₂ j
                  (a.truncate j)).val.truncate (f i) := by
                    rw [hparent]
            _ = (infiniteEnumCanonicalMap h₀ h₁ h₂ i
                  ((a.truncate j).truncate i)).val := hprev
            _ = (infiniteEnumCanonicalMap h₀ h₁ h₂ i
                  (a.truncate i)).val := by
                    rw [a.truncate_truncate hij0]
  exact hmain j i hij a

end CoordNode
end ThreeUniformDiaries
