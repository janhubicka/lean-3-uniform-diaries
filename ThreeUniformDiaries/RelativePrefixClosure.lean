import ThreeUniformDiaries.BranchTypeAgreement
import ThreeUniformDiaries.VectorTree

/-!
# Relative K_I is closed under initial segments

The K_I enumeration in Lemma Kiemb is required to put the proper
initialPart of a node before the node. This file proves concretely that
every positive shorter initialPart of a node of K_I again lies in K_I,
including the transition from an extension of I to a proper initialPart
of I.

All results are independent of the subsequent generic embedding.
-/

namespace ThreeUniformDiaries

namespace EnumerationBranchNode

/-- The finite initial segment of an enumeration branch node with last
ordinary vertex k. -/
def initialPart (A : EnumerationBranchNode) (k : Nat) :
    EnumerationBranchNode :=
  ⟨k, A.enumeration.truncate (k + 1)⟩

@[simp] theorem prefix_last (A : EnumerationBranchNode) (k : Nat) :
    (A.initialPart k).last = k := rfl

@[simp] theorem prefix_enum (A : EnumerationBranchNode) (k : Nat) :
    (A.initialPart k).enumeration = A.enumeration.truncate (k + 1) := rfl

theorem prefix_prefix (A : EnumerationBranchNode) (k l : Nat)
    (hkl : k ≤ l) :
    (A.initialPart l).initialPart k = A.initialPart k := by
  cases A with
  | mk last enumeration =>
      apply congrArg (fun e : EnumNode (k + 1) =>
        (⟨k, e⟩ : EnumerationBranchNode))
      exact EnumNode.truncate_truncate enumeration (Nat.succ_le_succ hkl)

theorem prefix_self (A : EnumerationBranchNode) :
    A.initialPart A.last = A := by
  cases A with
  | mk last enumeration =>
      simp [initialPart, EnumNode.truncate_self]

/-- The immediate predecessor as a finite initial segment. -/
def parent (A : EnumerationBranchNode) (h : 0 < A.last) :
    EnumerationBranchNode :=
  A.initialPart (A.last - 1)

theorem parent_last (A : EnumerationBranchNode) (h : 0 < A.last) :
    (A.parent h).last + 1 = A.last := by
  simp [parent, initialPart]
  omega

theorem parent_prefix (A : EnumerationBranchNode) (h : 0 < A.last) :
    A.enumeration.truncate ((A.parent h).last + 1) =
      (A.parent h).enumeration := by
  rfl

end EnumerationBranchNode

/-- Every initialPart of a relative K_I node is again in K_I. -/
theorem relativeBranch_prefix_mem
    {n : Nat} (I : EnumNode n) (A : RelativeBranchNode I)
    (k : Nat) (hk : k ≤ A.val.last) :
    InRelativeBranchGraph I (A.val.initialPart k) := by
  change
    (k + 1 < n →
      A.val.enumeration.truncate (k + 1) = I.truncate (k + 1)) ∧
    (n ≤ k + 1 →
      (A.val.enumeration.truncate (k + 1)).truncate n = I)
  constructor
  · intro hshort
    by_cases hAshort : A.val.last + 1 < n
    · have hprefix := A.property.1 hAshort
      rw [hprefix]
      exact EnumNode.truncate_truncate I (by omega)
    · have hAlong : n ≤ A.val.last + 1 := by omega
      have hprefix := A.property.2 hAlong
      calc
        A.val.enumeration.truncate (k + 1) =
            (A.val.enumeration.truncate n).truncate (k + 1) := by
              rw [EnumNode.truncate_truncate A.val.enumeration (by omega)]
        _ = I.truncate (k + 1) := by rw [hprefix]
  · intro hlarge
    have hAlong : n ≤ A.val.last + 1 := by omega
    rw [EnumNode.truncate_truncate A.val.enumeration hlarge]
    exact A.property.2 hAlong

/-- The canonical initialPart of a node in K_I, as another node of K_I. -/
noncomputable def relativeBranch_prefix
    {n : Nat} (I : EnumNode n) (A : RelativeBranchNode I)
    (k : Nat) (hk : k ≤ A.val.last) : RelativeBranchNode I :=
  ⟨A.val.initialPart k, relativeBranch_prefix_mem I A k hk⟩

@[simp] theorem relativeBranch_prefix_last
    {n : Nat} (I : EnumNode n) (A : RelativeBranchNode I)
    (k : Nat) (hk : k ≤ A.val.last) :
    (relativeBranch_prefix I A k hk).val.last = k := rfl

theorem relativeBranch_prefix_self
    {n : Nat} (I : EnumNode n) (A : RelativeBranchNode I) :
    relativeBranch_prefix I A A.val.last (le_refl _) = A := by
  apply Subtype.ext
  exact A.val.prefix_self

/-- All non-root nodes of K_I have a predecessor in the relative class
at the immediately preceding length. -/
theorem relativeBranch_exists_parent
    {n : Nat} (I : EnumNode n) (A : RelativeBranchNode I)
    (hA : 0 < A.val.last) :
    ∃ P : RelativeBranchNode I,
      P.val.last + 1 = A.val.last ∧
      A.val.enumeration.truncate (P.val.last + 1) =
        P.val.enumeration := by
  let k := A.val.last - 1
  have hk : k ≤ A.val.last := by omega
  refine ⟨relativeBranch_prefix I A k hk, ?_, ?_⟩
  · change k + 1 = A.val.last
    omega
  · rfl

/-- An initial segment of K_I is unique at every prescribed shorter
length, even when several other nodes have the same last index. -/
theorem relativeBranch_prefix_unique
    {n : Nat} (I : EnumNode n) (A P : RelativeBranchNode I)
    (hPA : P.val.last ≤ A.val.last)
    (hp : A.val.enumeration.truncate (P.val.last + 1) =
      P.val.enumeration) :
    P = relativeBranch_prefix I A P.val.last hPA := by
  apply Subtype.ext
  calc
    P.val = (⟨P.val.last, P.val.enumeration⟩ :
        EnumerationBranchNode) := by cases P.val; rfl
    _ = ⟨P.val.last,
        A.val.enumeration.truncate (P.val.last + 1)⟩ :=
      congrArg
        (fun e : EnumNode (P.val.last + 1) =>
          (⟨P.val.last, e⟩ : EnumerationBranchNode)) hp.symm
    _ = (relativeBranch_prefix I A P.val.last hPA).val := rfl

end ThreeUniformDiaries
