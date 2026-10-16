import ThreeUniformDiaries.DiaryOnePassConcreteCarrier

/-!
# Exact type-agreement decomposition across a finite event block

This file isolates the underlying finite-cut algebra for the ACTUAL
one-pass target. For arbitrary ordered 3-hypergraphs, equality of
1-types or auxiliary pair types through a later cut is equivalent
to equality at the earlier cut plus equality of every new test
whose column lies between the cuts.

Specialize to the concrete one-pass target. Every target index from
onePassBefore H m up to onePassOldImage H m is exactly one indexed
event of B_m. Consequently the change of singleton and auxiliary
pair types across the ENTIRE block is characterized by the edge
tests at ALL of those actual event vertices.

This is a direct, two-way target statement: no synthetic type codes,
no hypothetical prefix invariant, and no S1/S2 assumptions. The
next step is to use event roles and selected-class separation to
identify these tests with source normal/terminal germ refinements.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Decomposition of singleton-type agreement across a Nat interval:
all new singleton tests have their middle vertex inside [s,t). -/
theorem sameOneTypeBelow_interval_iff
    (K : Ordered3Graph Nat) (s t u v : Nat) (hst : s ≤ t) :
    K.SameOneTypeBelow t u v ↔
      K.SameOneTypeBelow s u v ∧
      (∀ a b : Nat, a < b → s ≤ b → b < t →
        (K.edge a b u ↔ K.edge a b v)) := by
  constructor
  · intro ht
    constructor
    · intro a b hab hb
      exact ht hab (by omega)
    · intro a b hab hsb hbt
      exact ht hab hbt
  · rintro ⟨hs, hnew⟩
    intro a b hab hb
    by_cases hbs : b < s
    · exact hs hab hbs
    · exact hnew a b hab (by omega) hb

/-- The auxiliary pair-type analogue: each new test is located
at the FIRST vertex of an increasing 3-uniform edge. -/
theorem sameAuxTypeBelow_interval_iff
    (K : Ordered3Graph Nat) (s t u₀ u₁ v₀ v₁ : Nat)
    (hst : s ≤ t) :
    K.SameAuxTypeBelow t u₀ u₁ v₀ v₁ ↔
      K.SameAuxTypeBelow s u₀ u₁ v₀ v₁ ∧
      (∀ a : Nat, s ≤ a → a < t →
        (K.edge a u₀ u₁ ↔ K.edge a v₀ v₁)) := by
  constructor
  · intro ht
    constructor
    · intro a ha
      exact ht (by omega)
    · intro a hsa hat
      exact ht hat
  · rintro ⟨hs, hnew⟩
    intro a ha
    by_cases has : a < s
    · exact hs has
    · exact hnew a (by omega) ha

/-- Full ordered-pair type agreement decomposes into its two
singleton coordinates and the auxiliary pair-coordinate. -/
theorem sameTwoTypeBelow_interval_iff
    (K : Ordered3Graph Nat)
    (s t u₀ u₁ v₀ v₁ : Nat) (hst : s ≤ t) :
    K.SameTwoTypeBelow t u₀ u₁ v₀ v₁ ↔
      K.SameTwoTypeBelow s u₀ u₁ v₀ v₁ ∧
      (∀ a b, a < b → s ≤ b → b < t →
        (K.edge a b u₀ ↔ K.edge a b v₀)) ∧
      (∀ a b, a < b → s ≤ b → b < t →
        (K.edge a b u₁ ↔ K.edge a b v₁)) ∧
      (∀ a, s ≤ a → a < t →
        (K.edge a u₀ u₁ ↔ K.edge a v₀ v₁)) := by
  change
    (K.SameOneTypeBelow t u₀ v₀ ∧
      K.SameOneTypeBelow t u₁ v₁ ∧
      K.SameAuxTypeBelow t u₀ u₁ v₀ v₁) ↔
    ((K.SameOneTypeBelow s u₀ v₀ ∧
      K.SameOneTypeBelow s u₁ v₁ ∧
      K.SameAuxTypeBelow s u₀ u₁ v₀ v₁) ∧
      (∀ a b, a < b → s ≤ b → b < t →
        (K.edge a b u₀ ↔ K.edge a b v₀)) ∧
      (∀ a b, a < b → s ≤ b → b < t →
        (K.edge a b u₁ ↔ K.edge a b v₁)) ∧
      (∀ a, s ≤ a → a < t →
        (K.edge a u₀ u₁ ↔ K.edge a v₀ v₁)))
  rw [K.sameOneTypeBelow_interval_iff s t u₀ v₀ hst,
    K.sameOneTypeBelow_interval_iff s t u₁ v₁ hst,
    K.sameAuxTypeBelow_interval_iff s t u₀ u₁ v₀ v₁ hst]
  tauto

end Ordered3Graph

namespace DiaryLeafPriority

open Ordered3Graph

/-- Every index in the target interval [before B_m, f(m)) is
an actual event of the unique finite block B_m. -/
theorem onePassBlock_event_at_every_interval_position
    (H : Ordered3Graph Nat) (m z : Nat)
    (hzStart : onePassBefore H m ≤ z)
    (hzEnd : z < onePassOldImage H m) :
    ∃ i : Fin (onePassBlock H m).length,
      onePassEventPosition H m i = z := by
  have hlt : z - onePassBefore H m < (onePassBlock H m).length := by
    dsimp [onePassOldImage, onePassBlockSize] at hzEnd
    omega
  refine ⟨⟨z - onePassBefore H m, hlt⟩, ?_⟩
  dsimp [onePassEventPosition]
  omega

/-- All singleton-type changes across one COMPLETE event block
are precisely the middle-column tests at its actual events. -/
theorem onePassBlock_oneType_interval_iff
    (H : Ordered3Graph Nat) (m u v : Nat) :
    (onePassRawTarget H).SameOneTypeBelow
        (onePassOldImage H m) u v ↔
      (onePassRawTarget H).SameOneTypeBelow
        (onePassBefore H m) u v ∧
      (∀ (i : Fin (onePassBlock H m).length) (a : Nat),
        a < onePassEventPosition H m i →
        ((onePassRawTarget H).edge a
            (onePassEventPosition H m i) u ↔
         (onePassRawTarget H).edge a
            (onePassEventPosition H m i) v)) := by
  have hst : onePassBefore H m ≤ onePassOldImage H m := by
    dsimp [onePassOldImage]
    omega
  rw [(onePassRawTarget H).sameOneTypeBelow_interval_iff
    (onePassBefore H m) (onePassOldImage H m) u v hst]
  constructor
  · rintro ⟨hbase, hnew⟩
    refine ⟨hbase, ?_⟩
    intro i a hai
    have hi := onePassEventPosition_interval H m i
    exact hnew a (onePassEventPosition H m i) hai hi.1 hi.2
  · rintro ⟨hbase, hnew⟩
    refine ⟨hbase, ?_⟩
    intro a b hab hstart hend
    obtain ⟨i, hi⟩ :=
      onePassBlock_event_at_every_interval_position
        H m b hstart hend
    rw [← hi]
    exact hnew i a (by simpa only [hi] using hab)

/-- All auxiliary pair-type changes across one COMPLETE event
block are precisely the first-coordinate edge tests at events. -/
theorem onePassBlock_auxType_interval_iff
    (H : Ordered3Graph Nat) (m u₀ u₁ v₀ v₁ : Nat) :
    (onePassRawTarget H).SameAuxTypeBelow
        (onePassOldImage H m) u₀ u₁ v₀ v₁ ↔
      (onePassRawTarget H).SameAuxTypeBelow
        (onePassBefore H m) u₀ u₁ v₀ v₁ ∧
      (∀ i : Fin (onePassBlock H m).length,
        ((onePassRawTarget H).edge
            (onePassEventPosition H m i) u₀ u₁ ↔
         (onePassRawTarget H).edge
            (onePassEventPosition H m i) v₀ v₁)) := by
  have hst : onePassBefore H m ≤ onePassOldImage H m := by
    dsimp [onePassOldImage]
    omega
  rw [(onePassRawTarget H).sameAuxTypeBelow_interval_iff
    (onePassBefore H m) (onePassOldImage H m)
    u₀ u₁ v₀ v₁ hst]
  constructor
  · rintro ⟨hbase, hnew⟩
    refine ⟨hbase, ?_⟩
    intro i
    have hi := onePassEventPosition_interval H m i
    exact hnew (onePassEventPosition H m i) hi.1 hi.2
  · rintro ⟨hbase, hnew⟩
    refine ⟨hbase, ?_⟩
    intro a hstart hend
    obtain ⟨i, hi⟩ :=
      onePassBlock_event_at_every_interval_position
        H m a hstart hend
    rw [← hi]
    exact hnew i

/-- Full 2-type agreement across one block is exactly
agreement beforehand plus BOTH singleton-coordinate event
columns and the auxiliary event tests. -/
theorem onePassBlock_twoType_interval_iff
    (H : Ordered3Graph Nat) (m u₀ u₁ v₀ v₁ : Nat) :
    (onePassRawTarget H).SameTwoTypeBelow
        (onePassOldImage H m) u₀ u₁ v₀ v₁ ↔
      (onePassRawTarget H).SameTwoTypeBelow
        (onePassBefore H m) u₀ u₁ v₀ v₁ ∧
      (∀ (i : Fin (onePassBlock H m).length) (a : Nat),
        a < onePassEventPosition H m i →
        ((onePassRawTarget H).edge a
            (onePassEventPosition H m i) u₀ ↔
         (onePassRawTarget H).edge a
            (onePassEventPosition H m i) v₀)) ∧
      (∀ (i : Fin (onePassBlock H m).length) (a : Nat),
        a < onePassEventPosition H m i →
        ((onePassRawTarget H).edge a
            (onePassEventPosition H m i) u₁ ↔
         (onePassRawTarget H).edge a
            (onePassEventPosition H m i) v₁)) ∧
      (∀ i : Fin (onePassBlock H m).length,
        ((onePassRawTarget H).edge
            (onePassEventPosition H m i) u₀ u₁ ↔
         (onePassRawTarget H).edge
            (onePassEventPosition H m i) v₀ v₁)) := by
  change
    ((onePassRawTarget H).SameOneTypeBelow
         (onePassOldImage H m) u₀ v₀ ∧
      (onePassRawTarget H).SameOneTypeBelow
         (onePassOldImage H m) u₁ v₁ ∧
      (onePassRawTarget H).SameAuxTypeBelow
         (onePassOldImage H m) u₀ u₁ v₀ v₁) ↔
    (((onePassRawTarget H).SameOneTypeBelow
         (onePassBefore H m) u₀ v₀ ∧
      (onePassRawTarget H).SameOneTypeBelow
         (onePassBefore H m) u₁ v₁ ∧
      (onePassRawTarget H).SameAuxTypeBelow
         (onePassBefore H m) u₀ u₁ v₀ v₁) ∧
      (∀ (i : Fin (onePassBlock H m).length) (a : Nat),
        a < onePassEventPosition H m i →
        ((onePassRawTarget H).edge a
            (onePassEventPosition H m i) u₀ ↔
         (onePassRawTarget H).edge a
            (onePassEventPosition H m i) v₀)) ∧
      (∀ (i : Fin (onePassBlock H m).length) (a : Nat),
        a < onePassEventPosition H m i →
        ((onePassRawTarget H).edge a
            (onePassEventPosition H m i) u₁ ↔
         (onePassRawTarget H).edge a
            (onePassEventPosition H m i) v₁)) ∧
      (∀ i : Fin (onePassBlock H m).length,
        ((onePassRawTarget H).edge
            (onePassEventPosition H m i) u₀ u₁ ↔
         (onePassRawTarget H).edge
            (onePassEventPosition H m i) v₀ v₁)))
  rw [onePassBlock_oneType_interval_iff H m u₀ v₀,
    onePassBlock_oneType_interval_iff H m u₁ v₁,
    onePassBlock_auxType_interval_iff H m u₀ u₁ v₀ v₁]
  tauto

end DiaryLeafPriority
end ThreeUniformDiaries
