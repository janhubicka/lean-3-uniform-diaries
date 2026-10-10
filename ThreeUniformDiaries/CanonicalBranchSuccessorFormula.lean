import ThreeUniformDiaries.CanonicalBranchComposition

/-!
# Identify the canonical branch prefix with the manuscript successor formula

The manuscript defines F_I on the universal branch vertex of length i+1
using a mapped predecessor enumeration and a mapped last singleton type.
The concise branch action is the prefix through the new selected vertex
of the full mapped enumeration. These definitions agree exactly.

This identity is a direct consequence of the verified full ambient
singleton-type compatibility and selected-level restriction fields,
so the proof is independent of which geometric strong subtree is used.
-/

namespace ThreeUniformDiaries
namespace CanonicalMap

/-- Full F_I formula for arbitrary finite branch vertices, with
the correct last selected target index. -/
theorem mapBranch_succ_formula (F : CanonicalMap)
    (B : EnumerationBranchNode) :
    (F.mapBranch B).enumeration =
      (F.mapEnum B.last (B.enumeration.truncate B.last)).succ
        (F.mapOne B.last (B.enumeration.oneType B.last B.last)) := by
  let H := F.mapEnum (B.last + 1) B.enumeration
  have hcut :
      H.truncate (F.level B.last) =
        F.mapEnum B.last (B.enumeration.truncate B.last) :=
    (F.truncate_compat B.enumeration (by omega)).symm
  have htype :
      H.oneType (F.level B.last) (F.level B.last) =
        F.mapOne B.last (B.enumeration.oneType B.last B.last) :=
    (F.oneType_compat B.enumeration (le_refl _) (Nat.lt_succ_self _)).symm
  apply EnumNode.ext_triples
  funext x y z
  change
    (H.truncate (F.level B.last + 1)).triple x y z =
      ((F.mapEnum B.last (B.enumeration.truncate B.last)).succ
        (F.mapOne B.last
          (B.enumeration.oneType B.last B.last))).triple x y z
  rw [H.truncate_succ_triple, hcut, htype]

end CanonicalMap
end ThreeUniformDiaries
