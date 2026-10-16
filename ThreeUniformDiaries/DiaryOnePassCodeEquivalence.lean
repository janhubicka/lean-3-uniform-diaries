import ThreeUniformDiaries.DiaryFlipPositiveTypeCodes
import ThreeUniformDiaries.DiaryOnePassTerminalGerms

/-!
# Exact finite representation of original 1-types and full 2-types

The one-pass completion construction partitions ORIGINAL leaves by
singleton types at a cut, and ordered leaf pairs by FULL two-types
at the cut. The finite Boolean code spaces used in the shared-node
audit are not merely invariants of the types: equality of their
codes is EXACTLY the manuscript's type-agreement relation.

The converse directions below were not part of the original
positive-witness code interface. They make the finite-code
description useful directly for the one-pass prefix induction.

The capped terminal-pair correspondence is reused from
DiaryOnePassTerminalGerms. This module does not claim a global
completed diary or protected flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- A finite singleton code represents the whole singleton
type, with no extra truncation or spurious identifications. -/
theorem oneCode_eq_iff_sameOneType
    (H : Ordered3Graph Nat) (m u v : Nat) :
    oneCode H m u = oneCode H m v ↔
      H.SameOneTypeBelow m u v := by
  constructor
  · intro h a b hab hb
    have ha : a < m := lt_trans hab hb
    have hAt := congrArg
      (fun code : OneCodeSpace m => code ⟨a, ha⟩ ⟨b, hb⟩) h
    simp only [oneCode, if_pos hab] at hAt
    by_cases hu : H.edge a b u <;>
      by_cases hv : H.edge a b v <;>
      simp_all
  · exact oneCode_eq_of_sameType H m u v

/-- The finite auxiliary code contains exactly the
incidence tests below the cut. -/
theorem auxCode_eq_iff_sameAuxType
    (H : Ordered3Graph Nat) (m u₀ u₁ v₀ v₁ : Nat) :
    auxCode H m u₀ u₁ = auxCode H m v₀ v₁ ↔
      H.SameAuxTypeBelow m u₀ u₁ v₀ v₁ := by
  constructor
  · intro h a ha
    have hAt := congrArg
      (fun code : AuxCodeSpace m => code ⟨a, ha⟩) h
    simp only [auxCode] at hAt
    by_cases hu : H.edge a u₀ u₁ <;>
      by_cases hv : H.edge a v₀ v₁ <;>
      simp_all
  · exact auxCode_eq_of_sameType H m u₀ u₁ v₀ v₁

/-- Crucial for one-pass completion: equality of the finite
FULL pair code is iff equality of the whole ordered 2-type.
In particular the two singleton components are included. -/
theorem twoCode_eq_iff_sameTwoType
    (H : Ordered3Graph Nat) (m u₀ u₁ v₀ v₁ : Nat) :
    twoCode H m u₀ u₁ = twoCode H m v₀ v₁ ↔
      H.SameTwoTypeBelow m u₀ u₁ v₀ v₁ := by
  constructor
  · intro h
    have hFirst : oneCode H m u₀ = oneCode H m v₀ := by
      simpa only [twoCode] using congrArg Prod.fst h
    have hSecond : oneCode H m u₁ = oneCode H m v₁ := by
      simpa only [twoCode] using congrArg (fun p : TwoCodeSpace m => p.2.1) h
    have hAux : auxCode H m u₀ u₁ = auxCode H m v₀ v₁ := by
      simpa only [twoCode] using congrArg (fun p : TwoCodeSpace m => p.2.2) h
    exact ⟨(oneCode_eq_iff_sameOneType H m u₀ v₀).mp hFirst,
      (oneCode_eq_iff_sameOneType H m u₁ v₁).mp hSecond,
      (auxCode_eq_iff_sameAuxType H m u₀ u₁ v₀ v₁).mp hAux⟩
  · exact twoCode_eq_of_sameType H m u₀ u₁ v₀ v₁

/-- A fixed original cut sees only finitely many possible
singletons signatures, even with infinitely many leaves. -/
theorem finite_realised_oneCodes
    (H : Ordered3Graph Nat) (m : Nat) :
    Finite {c : OneCodeSpace m // ∃ u : Nat, oneCode H m u = c} := by
  infer_instance

/-- Likewise every original cut has only finitely many
possible full ordered-pair signatures. -/
theorem finite_realised_twoCodes
    (H : Ordered3Graph Nat) (m : Nat) :
    Finite {c : TwoCodeSpace m // ∃ u v : Nat, twoCode H m u v = c} := by
  infer_instance

end DiaryLeafPriority
end ThreeUniformDiaries
