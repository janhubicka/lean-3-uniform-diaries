import ThreeUniformDiaries.DiaryPrediaryRoleNextCut
import ThreeUniformDiaries.DiaryOnePassCodeEquivalence

/-!
# Original split witnesses really separate finite child classes

The one-pass completion omits fresh events at a source split of the
corresponding arity. It is not enough to know that positive witnesses
have a common parent type (V1/V2 coherence): the ORIGINAL split must
also separate two distinct successor children in that parent. This
is proved here from the actual V/E pre-diary witness clauses, not from
S1/S2 of a completed diary.

The resulting finite-code corollaries connect the source split to
the same finite type codes used by the one-pass event blocks.
These lemmas do not construct the blocks or prove completion.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RolePrediary

variable {H : Ordered3Graph Nat}

/-- Every original 1-split has two later leaves in one old
singleton parent whose *new* split-incidence bits differ.
No S1/S2 assumptions are used. -/
theorem oneSplit_separates_old_parent_children
    (P : RolePrediary H) (m : Nat) (hm : IsOneSplit H m) :
    ∃ a b, IsLeaf H a ∧ IsLeaf H b ∧
      m < a ∧ m < b ∧
      H.SameOneTypeBelow m a b ∧
      ¬ (H.edge 0 m a ↔ H.edge 0 m b) := by
  classical
  obtain ⟨a, b, ha, hb, hma, hmb, hmeet⟩ :=
    P.one_split_witness m hm
  have hparent : H.SameOneTypeBelow m a b := by
    intro x y hxy hy
    exact (H.oneMeetLevel_agree a b) hxy (by omega)
  have hnext : ¬ H.SameOneTypeBelow (m + 1) a b := by
    intro h
    have hbound : m + 1 ≤ min a b := by omega
    have hle : m + 1 ≤ H.oneMeetLevel a b :=
      Nat.le_findGreatest hbound h
    omega
  have hbit : ¬ (H.edge 0 m a ↔ H.edge 0 m b) := by
    intro hsame
    exact hnext
      ((P.oneSplit_sameOneType_succ_iff m a b hm).mpr
        ⟨hparent, hsame⟩)
  exact ⟨a, b, ha, hb, hma, hmb, hparent, hbit⟩

/-- Every original 2-split has two later ordered leaf pairs in
the SAME original full pair parent, distinguished by the original
auxiliary split-incidence bit. -/
theorem twoSplit_separates_old_parent_children
    (P : RolePrediary H) (m : Nat) (hm : IsTwoSplit H m) :
    ∃ a b c d, a < b ∧ c < d ∧
      IsLeaf H a ∧ IsLeaf H b ∧
      IsLeaf H c ∧ IsLeaf H d ∧
      m < a ∧ m < c ∧
      H.SameTwoTypeBelow m a b c d ∧
      ¬ (H.edge m a b ↔ H.edge m c d) := by
  classical
  obtain ⟨a, b, c, d, hab, hcd,
    ha, hb, hc, hd, hma, hmc, hmeet⟩ :=
    P.two_split_witness m hm
  have hparent : H.SameTwoTypeBelow m a b c d := by
    have hfull := H.twoMeetLevel_agree a b c d
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy hy
      exact hfull.1 hxy (by omega)
    · intro x y hxy hy
      exact hfull.2.1 hxy (by omega)
    · intro x hx
      exact hfull.2.2 (by omega)
  have hnext : ¬ H.SameTwoTypeBelow (m + 1) a b c d := by
    intro h
    have hbound : m + 1 ≤ min a c := by omega
    have hle : m + 1 ≤ H.twoMeetLevel a b c d :=
      Nat.le_findGreatest hbound h
    omega
  have hbit : ¬ (H.edge m a b ↔ H.edge m c d) := by
    intro hsame
    exact hnext
      ((P.twoSplit_sameTwoType_succ_iff m a b c d hm).mpr
        ⟨hparent, hsame⟩)
  exact ⟨a, b, c, d, hab, hcd, ha, hb, hc, hd,
    hma, hmc, hparent, hbit⟩

/-- In the actual finite singleton codes, an old 1-split
refines at least one old parent into two different children. -/
theorem oneSplit_two_finite_code_children
    (P : RolePrediary H) (m : Nat) (hm : IsOneSplit H m) :
    ∃ a b, IsLeaf H a ∧ IsLeaf H b ∧
      m < a ∧ m < b ∧
      oneCode H m a = oneCode H m b ∧
      oneCode H (m + 1) a ≠ oneCode H (m + 1) b := by
  obtain ⟨a, b, ha, hb, hma, hmb, hparent, hbit⟩ :=
    P.oneSplit_separates_old_parent_children m hm
  refine ⟨a, b, ha, hb, hma, hmb,
    (oneCode_eq_iff_sameOneType H m a b).mpr hparent, ?_⟩
  intro hcode
  apply hbit
  exact ((P.oneSplit_sameOneType_succ_iff m a b hm).mp
    ((oneCode_eq_iff_sameOneType H (m + 1) a b).mp hcode)).2

/-- In the actual finite full pair codes, an old 2-split
refines at least one parent into two different children. -/
theorem twoSplit_two_finite_code_children
    (P : RolePrediary H) (m : Nat) (hm : IsTwoSplit H m) :
    ∃ a b c d, a < b ∧ c < d ∧
      IsLeaf H a ∧ IsLeaf H b ∧
      IsLeaf H c ∧ IsLeaf H d ∧
      m < a ∧ m < c ∧
      twoCode H m a b = twoCode H m c d ∧
      twoCode H (m + 1) a b ≠ twoCode H (m + 1) c d := by
  obtain ⟨a, b, c, d, hab, hcd, ha, hb, hc, hd,
    hma, hmc, hparent, hbit⟩ :=
    P.twoSplit_separates_old_parent_children m hm
  refine ⟨a, b, c, d, hab, hcd, ha, hb, hc, hd, hma, hmc,
    (twoCode_eq_iff_sameTwoType H m a b c d).mpr hparent, ?_⟩
  intro hcode
  apply hbit
  exact ((P.twoSplit_sameTwoType_succ_iff m a b c d hm).mp
    ((twoCode_eq_iff_sameTwoType H (m + 1) a b c d).mp hcode)).2

end RolePrediary
end DiaryLeafPriority
end ThreeUniformDiaries
