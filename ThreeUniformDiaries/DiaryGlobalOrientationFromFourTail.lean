import ThreeUniformDiaries.DiaryNativeOppositeTargetOrientation
import ThreeUniformDiaries.DiaryMarkerCutOrientation
import ThreeUniformDiaries.DiaryOrientationUniformSign

/-!
# Global diary orientation from one finite four-tail calibration

The former lower-bound gap was not the logical passage from
same-sign pair stabilisation to a uniform orientation: it was the
missing opposite-sign comparison. The latter is now expressed by
the actual four-tail native-source theorem.

Any pair of ordered diary-leaf comparisons has either equal
source signs, handled by the verified native I3 result at cut 3,
or opposite source signs, handled by the finite four-tail
calibration. Hence equality of source orientation bits is
equivalent to equality of stabilised target orientation bits.
There is one global preservation or reversal sign, even if one
or both orientation classes are empty; no additional density
or existence axiom is required.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph
open Ordered3Graph.UnorderedEmbedding

variable {H : Ordered3Graph Nat}

/-- Global relative lexicographic orientation is forced by the
actual four-tail I3 opposite-target witness. The initially
unordered outer embedding is allowed to reverse individual
comparisons before the verified fusion. -/
theorem stabilisedSource_global_relative_orientation
    (D : RoleDiary H)
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting) :
    ∀ p q : OrderedLeafPair H,
      (LexEarlier H p.first p.second ↔
       LexEarlier H q.first q.second) ↔
      (LexEarlier K
         (stabilisedSource G K F ψ p.first)
         (stabilisedSource G K F ψ p.second) ↔
       LexEarlier K
         (stabilisedSource G K F ψ q.first)
         (stabilisedSource G K F ψ q.second)) := by
  classical
  have hSame :
      ∀ p q : OrderedLeafPair H,
        (LexEarlier H p.first p.second ↔
         LexEarlier H q.first q.second) →
        (LexEarlier K
           (stabilisedSource G K F ψ p.first)
           (stabilisedSource G K F ψ p.second) ↔
         LexEarlier K
           (stabilisedSource G K F ψ q.first)
           (stabilisedSource G K F ψ q.second)) := by
    intro p q h
    exact D.stabilisedSource_lex_same_of_source_lex_same
      G K F ψ hψ
      p.first p.second q.first q.second
      p.first_lt_second q.first_lt_second
      p.first_is_leaf p.second_is_leaf
      q.first_is_leaf q.second_is_leaf h
  have hOpp :
      ∀ p q : OrderedLeafPair H,
        LexEarlier H p.first p.second →
        ¬ LexEarlier H q.first q.second →
        (LexEarlier K
           (stabilisedSource G K F ψ p.first)
           (stabilisedSource G K F ψ p.second) ↔
         ¬ LexEarlier K
           (stabilisedSource G K F ψ q.first)
           (stabilisedSource G K F ψ q.second)) := by
    intro p q hp hq
    exact D.oppositeLex_native_target_opposite_after_fusion
      G K F ψ hψ
      p.first p.second q.first q.second
      p.first_lt_second q.first_lt_second
      p.first_is_leaf p.second_is_leaf
      q.first_is_leaf q.second_is_leaf hp hq
  intro p q
  by_cases hp : LexEarlier H p.first p.second
  · by_cases hq : LexEarlier H q.first q.second
    · have heq := hSame p q (by tauto)
      tauto
    · have hopp := hOpp p q hp hq
      tauto
  · by_cases hq : LexEarlier H q.first q.second
    · have hopp := hOpp q p hq hp
      tauto
    · have heq := hSame p q (by tauto)
      tauto

/-- No non-emptiness assumption on diary orientation classes is
needed: relative agreement yields a single global preserve/flip
choice. If there are no ordered leaf pairs, preservation is
vacuous. -/
theorem stabilisedSource_global_uniform_lex_sign
    (D : RoleDiary H)
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting) :
    (∀ p : OrderedLeafPair H,
      LexEarlier H p.first p.second ↔
      LexEarlier K (stabilisedSource G K F ψ p.first)
        (stabilisedSource G K F ψ p.second)) ∨
    (∀ p : OrderedLeafPair H,
      LexEarlier H p.first p.second ↔
      ¬ LexEarlier K (stabilisedSource G K F ψ p.first)
        (stabilisedSource G K F ψ p.second)) := by
  classical
  by_cases h : Nonempty (OrderedLeafPair H)
  · obtain ⟨p⟩ := h
    exact global_lex_sign_of_relative
      (stabilisedSource G K F ψ) p
      (D.stabilisedSource_global_relative_orientation
        G K F ψ hψ)
  · left
    intro p
    exact False.elim (h ⟨p⟩)

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
