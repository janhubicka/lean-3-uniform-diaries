import ThreeUniformDiaries.DiaryMarkerCutOrientation
import ThreeUniformDiaries.DiaryPreembeddingSpec

/-!
# The full diary pre-embedding needs only a cross-class orientation witness

The source marker-cut identity and the checked gappy diary I3 already
show that ALL leaf-pair target lex orientations are constant within
either of the two source orientation classes.

Thus a single pair of representatives from DIFFERENT source classes
whose target orientations are different suffices for the complete
pre-embedding certificate, including marker roles, leaf edges,
singleton and full pair meets, and inclusion of leaf images in the
original unordered outer embedding's range.

A diary may in principle have only one occupied source orientation
class. In that degenerate case I3 alone is enough: no cross-class
witness is needed. We therefore also give the exact final statement:
IF both source classes are inhabited, assume only the EXISTENCE
of one opposite-target witness connecting them.

The difficult global cut-zero gadget/amalgamation work has now been
isolated to producing this single finite cross-class witness.
This module DOES NOT claim that existence unconditionally and does
not assert flip absorption or unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph
open Ordered3Graph.UnorderedEmbedding

/-- Pairwise orientation equivalence follows either from one
opposite-sign cross-class anchor or when only one source
orientation class exists. Constancy within each source class
is the single reusable hypothesis. -/
theorem relative_orientation_of_opposite_or_uniform
    {ι : Type*} (source target : ι → Prop)
    (hClass : ∀ x y, (source x ↔ source y) →
      (target x ↔ target y))
    (hCases :
      (∃ p q : ι, source p ∧ ¬ source q ∧
        (target p ↔ ¬ target q)) ∨
      (∀ x, source x) ∨ (∀ x, ¬ source x)) :
    ∀ x y, (source x ↔ source y) ↔
      (target x ↔ target y) := by
  rcases hCases with ⟨p, q, hp, hq, hop⟩ | hAll | hNone
  · exact relative_orientation_of_opposite_anchors
      source target p q hp hq hClass hop
  · intro x y
    have hs : source x ↔ source y :=
      iff_of_true (hAll x) (hAll y)
    exact iff_of_true hs (hClass x y hs)
  · intro x y
    have hs : source x ↔ source y :=
      iff_of_false (hNone x) (hNone y)
    exact iff_of_true hs (hClass x y hs)

namespace RoleDiary

variable {H : Ordered3Graph Nat}

/-- A single genuine opposite-sign target witness, whose source
pairs have opposite diary orientations, produces the COMPLETE
verified pre-embedding and the original outer leaf-range
inclusion. All other conditions are discharged by the existing
V/E/S, I2/I3, marker-cut and capped-meet theorems. -/
theorem chosenPreembedding_spec_of_opposite_anchor_pairs
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (hFleaf : ∀ t, IsLeaf K (F t))
    (D : RoleDiary H) (E : RoleDiary K)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (p q : OrderedLeafPair H)
    (hSourceP : LexEarlier H p.first p.second)
    (hSourceQ : ¬ LexEarlier H q.first q.second)
    (hTargetOpp :
      LexEarlier K (stabilisedSource G K F ψ p.first)
        (stabilisedSource G K F ψ p.second) ↔
      ¬ LexEarlier K (stabilisedSource G K F ψ q.first)
        (stabilisedSource G K F ψ q.second)) :
    DiaryPreembeddingSpec H K
      (D.chosenPreembedding G K F ψ) ∧
    (∀ u, IsLeaf H u →
      ∃ t, D.chosenPreembedding G K F ψ u = F t) := by
  have hGlobal :=
    stabilisedSource_global_relative_of_opposite_anchor_pairs
      G K F D ψ hψ p q hSourceP hSourceQ hTargetOpp
  have hMarker :
      ∀ a b c d : Nat, a < b → c < d →
        IsLeaf H a → IsLeaf H b →
        IsLeaf H c → IsLeaf H d →
        H.twoMeetLevel a b c d = 1 →
        ((LexEarlier H a b ↔ LexEarlier H c d) ↔
         (LexEarlier K (stabilisedSource G K F ψ a)
           (stabilisedSource G K F ψ b) ↔
          LexEarlier K (stabilisedSource G K F ψ c)
           (stabilisedSource G K F ψ d))) := by
    intro a b c d hab hcd ha hb hc hd _
    exact hGlobal
      ⟨a, b, hab, ha, hb⟩ ⟨c, d, hcd, hc, hd⟩
  exact D.chosenPreembedding_spec_and_leaf_range_of_relative_orientation
    G K F hFleaf E ψ hψ hMarker

/-- The exact final pre-embedding reduction: whenever both source
lex-orientation classes are inhabited, it suffices to construct
ONE opposite-sign target witness between them. If either source
class is empty, I3 already gives all relative orientations.

This is intentionally a conditional geometric witness premise,
not an axiom masquerading as the manuscript's orientation lemma.
-/
theorem chosenPreembedding_spec_of_cross_class_witness_when_needed
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (hFleaf : ∀ t, IsLeaf K (F t))
    (D : RoleDiary H) (E : RoleDiary K)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (hIfBoth :
      (∃ p : OrderedLeafPair H,
         LexEarlier H p.first p.second) →
      (∃ q : OrderedLeafPair H,
         ¬ LexEarlier H q.first q.second) →
      ∃ p q : OrderedLeafPair H,
        LexEarlier H p.first p.second ∧
        ¬ LexEarlier H q.first q.second ∧
        (LexEarlier K (stabilisedSource G K F ψ p.first)
          (stabilisedSource G K F ψ p.second) ↔
         ¬ LexEarlier K (stabilisedSource G K F ψ q.first)
          (stabilisedSource G K F ψ q.second))) :
    DiaryPreembeddingSpec H K
      (D.chosenPreembedding G K F ψ) ∧
    (∀ u, IsLeaf H u →
      ∃ t, D.chosenPreembedding G K F ψ u = F t) := by
  classical
  let source : OrderedLeafPair H → Prop :=
    fun p => LexEarlier H p.first p.second
  let target : OrderedLeafPair H → Prop :=
    fun p => LexEarlier K
      (stabilisedSource G K F ψ p.first)
      (stabilisedSource G K F ψ p.second)
  have hClass : ∀ p q : OrderedLeafPair H,
      (source p ↔ source q) → (target p ↔ target q) := by
    intro p q hpq
    exact D.stabilisedSource_lex_same_of_source_lex_same
      G K F ψ hψ p.first p.second q.first q.second
      p.first_lt_second q.first_lt_second
      p.first_is_leaf p.second_is_leaf
      q.first_is_leaf q.second_is_leaf hpq
  have hCases :
      (∃ p q : OrderedLeafPair H,
        source p ∧ ¬ source q ∧
        (target p ↔ ¬ target q)) ∨
      (∀ p, source p) ∨ (∀ p, ¬ source p) := by
    by_cases hp : ∃ p : OrderedLeafPair H, source p
    · by_cases hq : ∃ q : OrderedLeafPair H, ¬ source q
      · exact Or.inl (hIfBoth hp hq)
      · exact Or.inr (Or.inl (by
          intro p
          by_contra hneg
          exact hq ⟨p, hneg⟩))
    · exact Or.inr (Or.inr (by
        intro p hpos
        exact hp ⟨p, hpos⟩))
  have hGlobal :=
    relative_orientation_of_opposite_or_uniform
      source target hClass hCases
  have hMarker :
      ∀ a b c d : Nat, a < b → c < d →
        IsLeaf H a → IsLeaf H b →
        IsLeaf H c → IsLeaf H d →
        H.twoMeetLevel a b c d = 1 →
        ((LexEarlier H a b ↔ LexEarlier H c d) ↔
         (LexEarlier K (stabilisedSource G K F ψ a)
           (stabilisedSource G K F ψ b) ↔
          LexEarlier K (stabilisedSource G K F ψ c)
           (stabilisedSource G K F ψ d))) := by
    intro a b c d hab hcd ha hb hc hd _
    exact hGlobal
      ⟨a, b, hab, ha, hb⟩ ⟨c, d, hcd, hc, hd⟩
  exact D.chosenPreembedding_spec_and_leaf_range_of_relative_orientation
    G K F hFleaf E ψ hψ hMarker

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
