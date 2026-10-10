import ThreeUniformDiaries.FiniteCoupledCanonicalMapSucc

/-!
# Concrete finite canonical enumeration maps commute with restriction

The recursively constructed canonical enumeration map at selected
level f(j+1) has as its ancestor at f(j) exactly the canonical image
of the source predecessor enumeration. This follows directly from
its successor-cone law, even when target levels are skipped.

By induction, every earlier selected predecessor is preserved:
  (f₀^S(B)|f(i)) = f₀^S(B|i)   for i <= j.

Unlike the abstract CanonicalMap.truncate_compat field, this is a
theorem about the actual finite strong-picture construction. It is
the structural bridge needed for F_I^S to preserve the prescribed
initial I on every relative K_I vertex.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem finiteEnumCanonicalMap_parent
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : FiniteStrongPicture S₀ f k (.enum (f 0) r₀))
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (j : Nat) (hj : j < k) (a : EnumNode (j + 1)) :
    (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ (j + 1)
      (by omega) a).val.truncate (f j) =
      (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ j
        (Nat.le_of_lt hj) (a.truncate j)).val := by
  let p := finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ j
    (Nat.le_of_lt hj) (a.truncate j)
  let c := finiteStrongPicture_oneCanonicalMap h₁ h₂ j
    (Nat.le_of_lt hj) (a.boundaryOne j)
  have hcone := finiteStrongPicture_enumCanonicalMap_succ
    h₀ h₁ h₂ j hj (a.truncate j) (a.boundaryOne j)
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
          (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ (j + 1)
            (by omega) a).val :=
    CoordNode.le_trans hparent hcone
  have heq := htree.2
  change CoordNode.enum (f j)
      ((finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ (j + 1)
        (by omega) a).val.truncate (f j)) =
    CoordNode.enum (f j) p.val at heq
  cases heq
  rfl

theorem finiteEnumCanonicalMap_truncate
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : FiniteStrongPicture S₀ f k (.enum (f 0) r₀))
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (hf : StrictMono f)
    (i j : Nat) (hij : i ≤ j) (hjk : j ≤ k)
    (a : EnumNode j) :
    (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ j hjk a).val
      .truncate (f i) =
    (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i
      (by omega) (a.truncate i)).val := by
  have hmain :
      ∀ (j : Nat) (hjk : j ≤ k)
        (i : Nat) (hij : i ≤ j) (a : EnumNode j),
      (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ j hjk a).val
        .truncate (f i) =
      (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i
        (by omega) (a.truncate i)).val := by
    intro j
    induction j with
    | zero =>
        intro hjk i hij a
        have hi : i = 0 := by omega
        subst i
        simp only [EnumNode.truncate_self]
    | succ j ih =>
        intro hjk i hij a
        by_cases heq : i = j + 1
        · subst i
          simp only [EnumNode.truncate_self]
        · have hij0 : i ≤ j := by omega
          have hjlt : j < k := by omega
          have hparent :=
            finiteEnumCanonicalMap_parent h₀ h₁ h₂ j hjlt a
          have hprev := ih (by omega) i hij0 (a.truncate j)
          have hlevels : f i ≤ f j := hf.monotone hij0
          calc
            (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ (j + 1)
              (by omega) a).val.truncate (f i) =
              ((finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ (j + 1)
                (by omega) a).val.truncate (f j)).truncate (f i) := by
                  symm
                  exact EnumNode.truncate_truncate _ hlevels
            _ = (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ j
                  (by omega) (a.truncate j)).val.truncate (f i) := by
                    rw [hparent]
            _ = (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i
                  (by omega) ((a.truncate j).truncate i)).val :=
              hprev
            _ = (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i
                  (by omega) (a.truncate i)).val := by
                    rw [a.truncate_truncate hij0]
  exact hmain j hjk i hij a

end CoordNode
end ThreeUniformDiaries
