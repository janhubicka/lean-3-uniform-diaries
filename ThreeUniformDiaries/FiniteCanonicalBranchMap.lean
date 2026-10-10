import ThreeUniformDiaries.FiniteAembCanonicalImages
import ThreeUniformDiaries.FiniteAuxBranchEmbedding
import ThreeUniformDiaries.BranchHypergraph

/-!
# The concrete finite canonical map on the universal K_empty vertices

An EnumerationBranchNode is an arbitrary nonempty finite enumerated
hypergraph with a chosen last vertex. For each such node whose last
index lies in the finite source-height range, the manuscript's
canonical-map formula can be defined literally using the *constructed*
E0/E1 canonical maps on its predecessor and last-vertex 1-type:

  F^S(B) = succ₀ (f₀^S(B|last B), f₁^S(type_B^last B(last B))).

This defines F^S on ALL finite branch vertices up to the chosen
height, not only on the chosen source branch g_A. It does not yet
prove the map preserves the relative K_I carrier or induced edges.
-/

namespace ThreeUniformDiaries
namespace EnumNode

/-- Forming the singleton type at the last vertex is unaffected by
first restricting the finite source enumeration to that vertex. -/
theorem truncate_succ_oneType_last
    {m : Nat} (A : EnumNode m) (i : Nat) :
    (A.truncate (i + 1)).oneType i i = A.oneType i i := by
  apply OneNode.ext_pairs
  funext a b
  by_cases hb : b < i
  · simp [EnumNode.oneType, EnumNode.truncate, hb,
      Nat.lt_succ_self i]
  · simp [EnumNode.oneType, hb]

end EnumNode

namespace CoordNode

/-- Actual finite canonical-map formula, defined on every nonempty
branch vertex of last source index at most k. -/
noncomputable def finiteStrongPicture_branchMap
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : FiniteStrongPicture S₀ f k (.enum (f 0) r₀))
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (B : EnumerationBranchNode) (hB : B.last ≤ k) :
    EnumerationBranchNode :=
  ⟨f B.last,
    (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂
      B.last hB (B.enumeration.truncate B.last)).val.succ
    (finiteStrongPicture_oneCanonicalMap h₁ h₂
      B.last hB (B.enumeration.oneType B.last B.last)).val⟩

/-- The global finite formula specialises to the branch code of
an actual enumerated source A at any of its selected indices. -/
theorem finiteStrongPicture_branchMap_source
    {m : Nat} (A : EnumNode m)
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : FiniteStrongPicture S₀ f k (.enum (f 0) r₀))
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (i : Nat) (hi : i ≤ k) :
    finiteStrongPicture_branchMap h₀ h₁ h₂
      (A.toOrdered3Graph.branchNode i) (by simpa using hi) =
    (⟨f i,
      (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i hi
        (A.truncate i)).val.succ
      (finiteStrongPicture_oneCanonicalMap h₁ h₂ i hi
        (A.oneType i i)).val⟩ : EnumerationBranchNode) := by
  change (⟨f i,
      (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i hi
        ((A.toOrdered3Graph.initialSegment (i + 1)).truncate i)).val.succ
      (finiteStrongPicture_oneCanonicalMap h₁ h₂ i hi
        ((A.toOrdered3Graph.initialSegment (i + 1)).oneType i i)).val⟩ :
        EnumerationBranchNode) = _
  rw [A.toOrdered3Graph_initialSegment (i + 1)]
  rw [A.truncate_truncate (Nat.le_succ i)]
  rw [A.truncate_succ_oneType_last i]

end CoordNode
end ThreeUniformDiaries
