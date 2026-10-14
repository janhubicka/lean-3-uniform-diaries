import ThreeUniformDiaries.DiaryCanonicalTailInsertions

/-!
# Literal minimal meet-envelope formulas for pointed diary leaf pairs

There is no longer an existential/canonical-enumeration assumption.
The insertion maps are explicit strictly increasing maps which
fix the entire target prefix, and their selected carriers are
proved extensionally equal to the manuscript's displayed sets.

These theorems identify the least singleton/full-two-type-meet
closed carrier in the target. Translating that certificate into the
manuscript's named Envelope object and deriving source role shapes
from a comprehensive Diary structure are subsequent interfaces.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- The least meet-closed carrier of a type-respecting leaf pair
whose singleton meet precedes the protected cut is exactly the
protected target prefix plus the two endpoint images. -/
theorem two_tail_minimalMeetEnvelope_literal
    {H K : Ordered3Graph Nat}
    (ψ : Embedding H K) (hψ : ψ.TypeRespecting)
    (i a b : Nat) (hia : i ≤ a) (hab : a < b)
    (hearly : H.oneMeetLevel a b < i) :
    K.IsMinimalMeetEnvelope (ψ i) (ψ a) (ψ b)
      {x : Nat | x < ψ i ∨ x = ψ a ∨ x = ψ b} := by
  let f : Nat → Nat := twoTailInsertion (ψ i) (ψ a) (ψ b)
  have hf : StrictMono f :=
    twoTailInsertion_strictMono (ψ i) (ψ a) (ψ b)
      (ψ.strictMono.monotone hia) (ψ.strictMono hab)
  have hfix : ∀ t < ψ i, f t = t := by
    intro t ht
    exact twoTailInsertion_fix_prefix (ψ i) (ψ a) (ψ b) t ht
  have hfA : f (ψ i) = ψ a :=
    twoTailInsertion_first (ψ i) (ψ a) (ψ b)
  have hfB : f (ψ i+1) = ψ b :=
    twoTailInsertion_second (ψ i) (ψ a) (ψ b)
  have hmin :=
    two_tail_minimalMeetEnvelope_after_type_embedding
      ψ hψ i a b hearly f hf hfix hfA hfB
  have hcarrier :
      selectedCarrier f (ψ i+2) =
        {x : Nat | x < ψ i ∨ x = ψ a ∨ x = ψ b} := by
    ext x
    exact twoTailInsertion_carrier_iff (ψ i) (ψ a) (ψ b) x
  rw [hcarrier] at hmin
  exact hmin

/-- A 1-split/leaf diary pair has exactly the three-tail literal
minimal meet-envelope from the manuscript, even if the ambient
type-respecting image skips any number of target levels. -/
theorem role_three_tail_minimalMeetEnvelope_literal
    {H K : Ordered3Graph Nat}
    (shape : DiaryLeafPriority.SplitEdgeShape H)
    (ψ : Embedding H K) (hψ : ψ.TypeRespecting)
    (i m a b : Nat)
    (hi : 3 ≤ i) (him : i ≤ m)
    (hm : DiaryLeafPriority.IsOneSplit H m)
    (ha : DiaryLeafPriority.IsLeaf H a)
    (hb : DiaryLeafPriority.IsLeaf H b)
    (hab : a < b) (hma : m < a)
    (hmeet : H.oneMeetLevel a b = m) :
    K.IsMinimalMeetEnvelope (ψ i) (ψ a) (ψ b)
      {x : Nat |
        x < ψ i ∨ x = ψ m ∨ x = ψ a ∨ x = ψ b} := by
  let f : Nat → Nat := threeTailInsertion (ψ i) (ψ m) (ψ a) (ψ b)
  have hf : StrictMono f :=
    threeTailInsertion_strictMono (ψ i) (ψ m) (ψ a) (ψ b)
      (ψ.strictMono.monotone him) (ψ.strictMono hma)
      (ψ.strictMono hab)
  have hfix : ∀ t < ψ i, f t = t := by
    intro t ht
    exact threeTailInsertion_fix_prefix
      (ψ i) (ψ m) (ψ a) (ψ b) t ht
  have hfM : f (ψ i) = ψ m :=
    threeTailInsertion_split (ψ i) (ψ m) (ψ a) (ψ b)
  have hfA : f (ψ i+1) = ψ a :=
    threeTailInsertion_first (ψ i) (ψ m) (ψ a) (ψ b)
  have hfB : f (ψ i+2) = ψ b :=
    threeTailInsertion_second (ψ i) (ψ m) (ψ a) (ψ b)
  have hmin :=
    role_three_tail_minimalMeetEnvelope_after_type_embedding
      shape ψ hψ i m a b hi him hm ha hb hab hma hmeet
      f hf hfix hfM hfA hfB
  have hcarrier :
      selectedCarrier f (ψ i+3) =
        {x : Nat | x < ψ i ∨ x = ψ m ∨ x = ψ a ∨ x = ψ b} := by
    ext x
    exact threeTailInsertion_carrier_iff
      (ψ i) (ψ m) (ψ a) (ψ b) x
  rw [hcarrier] at hmin
  exact hmin

end Ordered3Graph
end ThreeUniformDiaries
