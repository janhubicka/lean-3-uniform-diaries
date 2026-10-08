import ThreeUniformDiaries.RelativeLevelFiniteness
import ThreeUniformDiaries.TypeRepresentation

/-!
# Every level of K_I is populated, with prescribed unique initial levels

Finite level sets alone do not construct a size-first enumeration: one
also needs nodes at arbitrarily large levels.  A canonical branch is
obtained by extending the fixed initial segment I with empty new triples.

For every k there is such a relative branch node of length k+1. On
levels below |I| it is the *only* possible K_I node, which is what
allows the first |I| images in Lemma Kiemb to be fixed to the identity.
-/

namespace ThreeUniformDiaries

/-- The canonical length-(k+1) node obtained from I by truncation or
extension by zero edges. -/
noncomputable def relativeBranchCanonical
    {n : Nat} (I : EnumNode n) (k : Nat) : RelativeBranchNode I := by
  let A : EnumerationBranchNode := ⟨k, I.truncate (k + 1)⟩
  have hrel : InRelativeBranchGraph I A := by
    constructor
    · intro hshort
      rfl
    · intro hlarge
      change (I.truncate (k + 1)).truncate n = I
      exact (EnumNode.truncate_truncate I hlarge).trans
        (EnumNode.truncate_self I)
  exact ⟨A, hrel⟩

@[simp] theorem relativeBranchCanonical_last
    {n : Nat} (I : EnumNode n) (k : Nat) :
    (relativeBranchCanonical I k).val.last = k := rfl

@[simp] theorem relativeBranchCanonical_enum
    {n : Nat} (I : EnumNode n) (k : Nat) :
    (relativeBranchCanonical I k).val.enumeration = I.truncate (k + 1) := rfl

/-- In particular the relative universal branch hypergraph is
nonempty on every finite enumeration level. -/
theorem relativeBranch_level_nonempty
    {n : Nat} (I : EnumNode n) (k : Nat) :
    ∃ A : RelativeBranchNode I, A.val.last = k :=
  ⟨relativeBranchCanonical I k, rfl⟩

/-- The canonical nodes form a chain of initial segments. -/
theorem relativeBranchCanonical_chain
    {n : Nat} (I : EnumNode n) (k l : Nat) (hkl : k ≤ l) :
    (relativeBranchCanonical I l).val.enumeration.truncate (k + 1) =
      (relativeBranchCanonical I k).val.enumeration := by
  change (I.truncate (l + 1)).truncate (k + 1) =
    I.truncate (k + 1)
  exact EnumNode.truncate_truncate I (Nat.succ_le_succ hkl)

/-- On levels strictly below n, the prescribed I-prefix is the only
possible node of relative K_I. -/
theorem relativeBranch_initial_unique
    {n : Nat} (I : EnumNode n) (k : Nat) (hk : k < n)
    (A : RelativeBranchNode I) (hA : A.val.last = k) :
    A = relativeBranchCanonical I k := by
  rcases A with ⟨⟨last, E⟩, hrel⟩
  change last = k at hA
  subst last
  have hE : E = I.truncate (k + 1) := by
    by_cases hshort : k + 1 < n
    · exact hrel.1 hshort
    · have hn : k + 1 = n := by omega
      subst n
      have heq := hrel.2 (le_refl (k + 1))
      rw [EnumNode.truncate_self E] at heq
      exact heq.trans (EnumNode.truncate_self I).symm
  cases hE
  rfl

end ThreeUniformDiaries
