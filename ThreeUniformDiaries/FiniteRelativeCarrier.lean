import ThreeUniformDiaries.FiniteCanonicalInitialCut
import ThreeUniformDiaries.FiniteRelativeFixedBranch

/-!
# The finite canonical branch map preserves the entire relative K_I carrier

For any finite strong vector picture with all first n coordinate levels
present and level map fixing every j<n, the constructed canonical map
F^S sends EVERY relative branch vertex of K_I of source last index <=k
back into K_I. This includes vertices not on the selected copy of A.

Case last<n: F^S fixes the entire branch vertex literally.
Case last>=n: the source initial n-prefix is I; the concrete E0
canonical map preserves that prefix even across the first skipped
target interval, and adding the last target vertex does not change it.

This is the full-domain carrier statement needed for the manuscript's
definition F_I^S : K_I^{<=k+1} -> K_I. It uses neither an abstract
CanonicalMap compatibility field nor any artificial source vertices.
-/

namespace ThreeUniformDiaries

namespace CoordNode

private theorem strictMono_nat_id_le
    (f : Nat → Nat) (hf : StrictMono f) (j : Nat) :
    j ≤ f j := by
  induction j with
  | zero => omega
  | succ i ih =>
      have hstep : f i + 1 ≤ f (i + 1) := by
        simpa only [Nat.succ_eq_add_one] using
          (Nat.succ_le_of_lt (hf (Nat.lt_succ_self i)))
      omega

theorem finiteBranchMap_preserves_relative_carrier
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {k n : Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : FiniteStrongPicture S₀ f k (.enum (f 0) r₀))
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (hf : StrictMono f)
    (hfix : ∀ i < n, f i = i)
    (hn : n ≤ k + 1)
    (hfull₀ : ∀ a : EnumNode 0, CoordNode.enum 0 a ∈ S₀)
    (hfull₁ : ∀ a : OneNode 0, CoordNode.one 0 a ∈ S₁)
    (hfull₂ : ∀ a : AuxNode 0, CoordNode.aux 0 a ∈ S₂)
    (I : EnumNode n) (B : EnumerationBranchNode)
    (hB : B.last ≤ k)
    (hrel : InRelativeBranchGraph I B) :
    InRelativeBranchGraph I (finiteStrongPicture_branchMap h₀ h₁ h₂ B hB) := by
  by_cases hj : B.last < n
  · have hsame := finiteBranchMap_fixed_before_n
      h₀ h₁ h₂ hfix hn hfull₀ hfull₁ hfull₂ B hB hj
    simpa only [hsame] using hrel
  · have hnj : n ≤ B.last := Nat.le_of_not_gt hj
    have hindex : B.last ≤ f B.last := strictMono_nat_id_le f hf B.last
    have hnf : n ≤ f B.last := by omega
    constructor
    · intro hsmall
      change f B.last + 1 < n at hsmall
      omega
    · intro _
      let pred := B.enumeration.truncate B.last
      have hpre :
          (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂
            B.last hB pred).val.truncate n = I := by
        calc
          (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂
            B.last hB pred).val.truncate n = pred.truncate n :=
              finiteEnumCanonicalMap_preserves_initial_cut
                h₀ h₁ h₂ hf hfix (by omega)
                hfull₀ hfull₁ hfull₂ B.last hnj hB pred
          _ = B.enumeration.truncate n :=
            EnumNode.truncate_truncate B.enumeration hnj
          _ = I := hrel.2 (by omega)
      change
        ((finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂
          B.last hB pred).val.succ
        (finiteStrongPicture_oneCanonicalMap h₁ h₂
          B.last hB (B.enumeration.oneType B.last B.last)).val).truncate n = I
      calc
        ((finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂
          B.last hB pred).val.succ
          (finiteStrongPicture_oneCanonicalMap h₁ h₂
            B.last hB (B.enumeration.oneType B.last B.last)).val).truncate n =
          (((finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂
            B.last hB pred).val.succ
            (finiteStrongPicture_oneCanonicalMap h₁ h₂
              B.last hB (B.enumeration.oneType B.last B.last)).val).truncate (f B.last)).truncate n := by
                  symm
                  exact EnumNode.truncate_truncate _ hnf
        _ = (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂
              B.last hB pred).val.truncate n := by
                rw [EnumNode.truncate_succ]
        _ = I := hpre

/-- The concrete canonical map as a well-defined map of relative K_I
vertices, over the entire finite-height domain. -/
noncomputable def finiteRelativeBranchMap
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {k n : Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : FiniteStrongPicture S₀ f k (.enum (f 0) r₀))
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (hf : StrictMono f)
    (hfix : ∀ i < n, f i = i)
    (hn : n ≤ k + 1)
    (hfull₀ : ∀ a : EnumNode 0, CoordNode.enum 0 a ∈ S₀)
    (hfull₁ : ∀ a : OneNode 0, CoordNode.one 0 a ∈ S₁)
    (hfull₂ : ∀ a : AuxNode 0, CoordNode.aux 0 a ∈ S₂)
    (I : EnumNode n)
    (B : RelativeBranchNode I) (hB : B.val.last ≤ k) :
    RelativeBranchNode I :=
  ⟨finiteStrongPicture_branchMap h₀ h₁ h₂ B.val hB,
    finiteBranchMap_preserves_relative_carrier
      h₀ h₁ h₂ hf hfix hn hfull₀ hfull₁ hfull₂
      I B.val hB B.property⟩

end CoordNode
end ThreeUniformDiaries
