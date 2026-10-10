import ThreeUniformDiaries.CanonicalBranchComposition
import ThreeUniformDiaries.RelativeBranchHypergraph

/-!
# Relative K_I carrier under canonical branch maps

A canonical map F fixes the initial finite hypergraph I in the
required sense when all selected vertex positions strictly below n
are unchanged and the image of I itself has first n vertices I.
The selected level F.level n may be strictly larger than n: this is
why asking F.mapEnum n I = I would be the wrong condition.

Under precisely this cut condition, the canonical map on universal
branch vertices restricts to an actual map on the entire carrier K_I.
The proof covers arbitrary vertices of the carrier, not merely
branch vertices coming from an enumerated copy of A.
-/

namespace ThreeUniformDiaries
namespace CanonicalMap

private theorem level_ge (F : CanonicalMap) (n : Nat) :
    n ≤ F.level n := by
  induction n with
  | zero => omega
  | succ k ih =>
    have hs := F.strictMono (Nat.lt_succ_self k)
    omega

/-- A fixed initial segment I need not have F.level n = n. -/
def FixesRelativeCut (F : CanonicalMap) {n : Nat}
    (I : EnumNode n) : Prop :=
  (∀ j < n, F.level j = j) ∧
  (F.mapEnum n I).truncate n = I

/-- The map on all universal enumeration branches preserves the full
relative K_I carrier whenever it fixes the original initial segment. -/
theorem mapBranch_preserves_relative
    (F : CanonicalMap) {n : Nat} (I : EnumNode n)
    (hfix : F.FixesRelativeCut I)
    (B : EnumerationBranchNode)
    (hrel : InRelativeBranchGraph I B) :
    InRelativeBranchGraph I (F.mapBranch B) := by
  rcases hfix with ⟨hlev, hroot⟩
  constructor
  · intro hsmallTarget
    have hsmall : B.last + 1 < n := by
      have hge := F.level_ge B.last
      change F.level B.last + 1 < n at hsmallTarget
      omega
    have hFi : F.level B.last = B.last := hlev B.last (by omega)
    have hFnext : F.level (B.last + 1) = B.last + 1 :=
      hlev (B.last + 1) hsmall
    have hB : B.enumeration = I.truncate (B.last + 1) :=
      hrel.1 hsmall
    have hshort :
        F.mapEnum (B.last + 1) (I.truncate (B.last + 1)) =
        I.truncate (B.last + 1) := by
      calc
        F.mapEnum (B.last + 1) (I.truncate (B.last + 1)) =
          (F.mapEnum n I).truncate (F.level (B.last + 1)) :=
            F.truncate_compat I (by omega)
        _ = (F.mapEnum n I).truncate (B.last + 1) := by
          rw [hFnext]
        _ = ((F.mapEnum n I).truncate n).truncate (B.last + 1) :=
          (EnumNode.truncate_truncate _ (by omega)).symm
        _ = I.truncate (B.last + 1) := by rw [hroot]
    change
      (F.mapEnum (B.last + 1) B.enumeration).truncate
          (F.level B.last + 1) =
      I.truncate (F.level B.last + 1)
    rw [hFi, hB, hshort]
    exact EnumNode.truncate_self _
  · intro hlargeTarget
    have hlarge : n ≤ B.last + 1 := by
      by_contra hn
      have hsmall : B.last + 1 < n := by omega
      have hj : B.last < n := by omega
      have hFi := hlev B.last hj
      change n ≤ F.level B.last + 1 at hlargeTarget
      omega
    have hsrc : B.enumeration.truncate n = I :=
      hrel.2 hlarge
    have hFnn : n ≤ F.level n := F.level_ge n
    have hFnB : n ≤ F.level B.last + 1 := by
      have hge := F.level_ge B.last
      omega
    have hraw :
        (F.mapEnum (B.last + 1) B.enumeration).truncate n = I := by
      calc
        (F.mapEnum (B.last + 1) B.enumeration).truncate n =
          ((F.mapEnum (B.last + 1) B.enumeration).truncate
            (F.level n)).truncate n :=
              (EnumNode.truncate_truncate _ hFnn).symm
        _ = (F.mapEnum n (B.enumeration.truncate n)).truncate n := by
          rw [← F.truncate_compat B.enumeration hlarge]
        _ = I := by rw [hsrc, hroot]
    change
      ((F.mapEnum (B.last + 1) B.enumeration).truncate
        (F.level B.last + 1)).truncate n = I
    rw [EnumNode.truncate_truncate _ hFnB]
    exact hraw

/-- The resulting actual endomap of the full relative branch carrier. -/
noncomputable def relativeMapBranch
    (F : CanonicalMap) {n : Nat} (I : EnumNode n)
    (hfix : F.FixesRelativeCut I)
    (B : RelativeBranchNode I) : RelativeBranchNode I :=
  ⟨F.mapBranch B.val,
   F.mapBranch_preserves_relative I hfix B.val B.property⟩

@[simp] theorem relativeMapBranch_val
    (F : CanonicalMap) {n : Nat} (I : EnumNode n)
    (hfix : F.FixesRelativeCut I)
    (B : RelativeBranchNode I) :
    (F.relativeMapBranch I hfix B).val = F.mapBranch B.val := rfl

end CanonicalMap
end ThreeUniformDiaries
