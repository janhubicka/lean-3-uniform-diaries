import ThreeUniformDiaries.FiniteCanonicalBranchMap
import ThreeUniformDiaries.FiniteCanonicalFixedPrefix
import ThreeUniformDiaries.RelativeBranchHypergraph

/-!
# Canonical maps on relative branch vertices below the fixed prefix

For any finite enumeration B of length j+1, the one-type of its last
vertex over j is its successor parameter boundaryOne j. This
identifies the manuscript's F map with the elementary decomposition
of B into its predecessor enumeration and its last-vertex 1-type.

When j<n and the first n coordinate levels are fixed, the
constructed canonical map fixes B *literally*. This is required
also for relative K_I branch vertices shorter than I.
-/

namespace ThreeUniformDiaries

namespace EnumNode

theorem oneType_last_eq_boundaryOne {j : Nat} (B : EnumNode (j + 1)) :
    B.oneType j j = B.boundaryOne j := by
  apply OneNode.ext_pairs
  funext a b
  by_cases hb : b < j
  · by_cases ha : a < b
    · simp [EnumNode.oneType, EnumNode.boundaryOne, hb, ha]
    · have hzero : B.triple a b j = false :=
        B.support a b j (by
          intro h
          exact ha h.1)
      simp [EnumNode.oneType, EnumNode.boundaryOne, hb, ha, hzero]
  · simp [EnumNode.oneType, EnumNode.boundaryOne, hb]

end EnumNode

namespace CoordNode

theorem finiteBranchMap_fixed_of_coordinate_maps
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : FiniteStrongPicture S₀ f k (.enum (f 0) r₀))
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (B : EnumerationBranchNode) (hB : B.last ≤ k)
    (hfj : f B.last = B.last)
    (hEnum : CoordNode.enum (f B.last)
      (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂
        B.last hB (B.enumeration.truncate B.last)).val =
      CoordNode.enum B.last (B.enumeration.truncate B.last))
    (hOne : CoordNode.one (f B.last)
      (finiteStrongPicture_oneCanonicalMap h₁ h₂
        B.last hB (B.enumeration.oneType B.last B.last)).val =
      CoordNode.one B.last (B.enumeration.oneType B.last B.last)) :
    finiteStrongPicture_branchMap h₀ h₁ h₂ B hB = B := by
  rcases B with ⟨j, A⟩
  change f j = j at hfj
  rw [hfj] at hEnum hOne
  injection hEnum with he
  injection hOne with ho
  change (⟨f j,
      (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂
        j hB (A.truncate j)).val.succ
      (finiteStrongPicture_oneCanonicalMap h₁ h₂
        j hB (A.oneType j j)).val⟩ : EnumerationBranchNode) =
        ⟨j, A⟩
  rw [hfj, he, ho, A.oneType_last_eq_boundaryOne]
  simp only [EnumNode.succ_truncate_boundary]

/-- Every relative K_I branch vertex of last index below the fixed
prefix is fixed, not merely vertices of the selected source copy. -/
theorem finiteBranchMap_fixed_before_n
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {k n : Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : FiniteStrongPicture S₀ f k (.enum (f 0) r₀))
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (hfix : ∀ i < n, f i = i)
    (hn : n ≤ k + 1)
    (hfull₀ : ∀ a : EnumNode 0, CoordNode.enum 0 a ∈ S₀)
    (hfull₁ : ∀ a : OneNode 0, CoordNode.one 0 a ∈ S₁)
    (hfull₂ : ∀ a : AuxNode 0, CoordNode.aux 0 a ∈ S₂)
    (B : EnumerationBranchNode)
    (hB : B.last ≤ k) (hj : B.last < n) :
    finiteStrongPicture_branchMap h₀ h₁ h₂ B hB = B := by
  obtain ⟨_, hOne, hEnum⟩ :=
    finiteCanonicalMaps_fixedPrefix h₀ h₁ h₂
      hfix hn hfull₀ hfull₁ hfull₂
  exact finiteBranchMap_fixed_of_coordinate_maps
    h₀ h₁ h₂ B hB (hfix B.last hj)
    (hEnum B.last hj _) (hOne B.last hj _)

end CoordNode
end ThreeUniformDiaries
