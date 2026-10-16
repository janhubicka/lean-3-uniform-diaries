import ThreeUniformDiaries.DiaryPrediaryDefinition
import Mathlib

/-!
# Finite positive-type signatures required at shared diary split vertices

The original flip-prefix tree identifies source split vertices on the
basis of earlier flip-control bits. That is unsound: different flips
can have incompatible positively incident pair types already at
marker 1, despite having the same prefix of flip controls.

At a 1-split, the type through its level of EVERY positive incident
leaf has the same finite Boolean code. At a 2-split, the full 2-type
of EVERY positive incident ordered leaf pair has the same finite code.
These are consequences of the literal V1 and V2 pre-diary axioms.

Thus a revised shared-split node may carry this positive profile as
a necessary finite-state compatibility key. This module proves
finiteness and witness-independence; it DOES NOT assert that adding
such keys completes the flip amalgamation or protects mixed meets.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- Singleton type codes at a cut m, including only increasing
earlier pairs and zero elsewhere. -/
abbrev OneCodeSpace (m : Nat) := Fin m → Fin m → Bool

/-- Auxiliary component of an ordered pair type at cut m. -/
abbrev AuxCodeSpace (m : Nat) := Fin m → Bool

/-- Full ordered pair type code with both singleton components. -/
abbrev TwoCodeSpace (m : Nat) :=
  OneCodeSpace m × (OneCodeSpace m × AuxCodeSpace m)

noncomputable def oneCode
    (H : Ordered3Graph Nat) (m u : Nat) : OneCodeSpace m := by
  classical
  exact fun a b =>
    if a.val < b.val then decide (H.edge a.val b.val u) else false

noncomputable def auxCode
    (H : Ordered3Graph Nat) (m u v : Nat) : AuxCodeSpace m := by
  classical
  exact fun a => decide (H.edge a.val u v)

noncomputable def twoCode
    (H : Ordered3Graph Nat) (m u v : Nat) : TwoCodeSpace m :=
  (oneCode H m u, (oneCode H m v, auxCode H m u v))

/-- The two finite code spaces really are finite at every source
level, even for a countably infinite family of flip branches. -/
theorem finite_oneCodeSpace (m : Nat) :
    Finite (OneCodeSpace m) := by
  infer_instance

theorem finite_twoCodeSpace (m : Nat) :
    Finite (TwoCodeSpace m) := by
  infer_instance

theorem oneCode_eq_of_sameType
    (H : Ordered3Graph Nat) (m u v : Nat)
    (h : H.SameOneTypeBelow m u v) :
    oneCode H m u = oneCode H m v := by
  classical
  funext a b
  by_cases hab : a.val < b.val
  · have htest := h hab b.isLt
    simp [oneCode, hab, htest]
  · simp [oneCode, hab]

theorem auxCode_eq_of_sameType
    (H : Ordered3Graph Nat) (m u₀ u₁ v₀ v₁ : Nat)
    (h : H.SameAuxTypeBelow m u₀ u₁ v₀ v₁) :
    auxCode H m u₀ u₁ = auxCode H m v₀ v₁ := by
  classical
  funext a
  have htest := h a.isLt
  by_cases hp : H.edge a.val u₀ u₁
  · have hq : H.edge a.val v₀ v₁ := htest.mp hp
    simp [auxCode, hp, hq]
  · have hq : ¬ H.edge a.val v₀ v₁ := by
      intro hq
      exact hp (htest.mpr hq)
    simp [auxCode, hp, hq]

theorem twoCode_eq_of_sameType
    (H : Ordered3Graph Nat) (m u₀ u₁ v₀ v₁ : Nat)
    (h : H.SameTwoTypeBelow m u₀ u₁ v₀ v₁) :
    twoCode H m u₀ u₁ = twoCode H m v₀ v₁ := by
  rcases h with ⟨hFirst, hSecond, hAux⟩
  dsimp only [twoCode]
  exact congrArg₂ (fun a b => (a,b))
    (oneCode_eq_of_sameType H m u₀ v₀ hFirst)
    (congrArg₂ (fun a b => (a,b))
      (oneCode_eq_of_sameType H m u₁ v₁ hSecond)
      (auxCode_eq_of_sameType H m u₀ u₁ v₀ v₁ hAux))

/-- V1 makes the code of positive singleton witnesses independent
of which positively incident leaf was used to read it. -/
theorem positive_oneSplit_code_unique
    {H : Ordered3Graph Nat} (P : RolePrediary H)
    (m a b : Nat)
    (hm : IsOneSplit H m)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hPosA : H.edge 0 m a) (hPosB : H.edge 0 m b) :
    oneCode H m a = oneCode H m b := by
  exact oneCode_eq_of_sameType H m a b
    (P.one_split_coherent m a b hm ha hb hPosA hPosB)

/-- V2 makes the entire full pair-code profile of positive
witnesses independent of the pair used to read it.
In particular marker-one aux bits cannot disagree. -/
theorem positive_twoSplit_code_unique
    {H : Ordered3Graph Nat} (P : RolePrediary H)
    (m a b c d : Nat)
    (hm : IsTwoSplit H m)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hPosAB : H.edge m a b) (hPosCD : H.edge m c d) :
    twoCode H m a b = twoCode H m c d := by
  exact twoCode_eq_of_sameType H m a b c d
    (P.two_split_coherent m a b c d hm hab hcd
      ha hb hc hd hPosAB hPosCD)

end DiaryLeafPriority
end ThreeUniformDiaries
