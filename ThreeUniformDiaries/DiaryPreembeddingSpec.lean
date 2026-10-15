import ThreeUniformDiaries.DiaryChosenPreembeddingRoles
import ThreeUniformDiaries.DiaryChosenLeafOneMeets
import ThreeUniformDiaries.DiaryChosenLeafPairMeetCases
import ThreeUniformDiaries.DiaryMarkerOnePairReduction
import ThreeUniformDiaries.DiaryChosenLeafImageRange

/-!
# The exact diary pre-embedding interface and its remaining orientation input

We explicitly package the requirements of the manuscript's
diary-pre-embedding definition on enumerated 3-uniform diaries:

* strict increase and identity on the three initial marker vertices;
* preservation of all three V-roles (leaf / one-split / two-split);
* preservation AND reflection of induced hyperedges among leaves;
* literal preservation of singleton-type meets of all source leaves;
* literal preservation of full 2-type meets of all increasing
  ordered pairs of source leaves.

The actual chosen map already satisfies every item except the
pair-meet case at marker 1. This module states and verifies the
complete specification under precisely the RELATIVE LEXICOGRAPHIC
ORIENTATION condition needed for marker 1. Comparing equality of
two lex orientation bits allows a simultaneous global reversal.

Every mathematical condition in the other cases is discharged:
the target leaf-roles follow from the image of the original
UNORDERED outer embedding, singleton meets from I2, genuine
two-split meets from I3, and capped pair meets from the later
chosen one-split image. The final theorem also includes that
all source leaf images lie in the original outer F-image.

This is a CONDITIONAL result, not the as-yet-unproved global
cut-zero orientation synchronisation, flip theorem or lower bound.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph
open Ordered3Graph.UnorderedEmbedding

/-- The manuscript's diary-pre-embedding conditions, restricted to
the role and leaf-type primitives already formalised for structures
on Nat. The lexicographic orders themselves are not an extra
pre-embedding condition, since flips subsequently adjust them. -/
structure DiaryPreembeddingSpec
    (H K : Ordered3Graph Nat) (θ : Nat → Nat) : Prop where
  strictMono : StrictMono θ
  marker_zero : θ 0 = 0
  marker_one : θ 1 = 1
  marker_two : θ 2 = 2
  leaf_role : ∀ u, IsLeaf H u → IsLeaf K (θ u)
  one_split_role : ∀ i, IsOneSplit H i → IsOneSplit K (θ i)
  two_split_role : ∀ i, IsTwoSplit H i → IsTwoSplit K (θ i)
  leaf_edge_iff :
    ∀ a b c, a < b → b < c →
      IsLeaf H a → IsLeaf H b → IsLeaf H c →
      (H.edge a b c ↔ K.edge (θ a) (θ b) (θ c))
  leaf_one_meet :
    ∀ u v, IsLeaf H u → IsLeaf H v →
      K.oneMeetLevel (θ u) (θ v) = θ (H.oneMeetLevel u v)
  leaf_two_meet :
    ∀ a b c d, a < b → c < d →
      IsLeaf H a → IsLeaf H b →
      IsLeaf H c → IsLeaf H d →
      K.twoMeetLevel (θ a) (θ b) (θ c) (θ d) =
        θ (H.twoMeetLevel a b c d)

namespace RoleDiary

variable {H : Ordered3Graph Nat}

/-- Once relative lexicographic orientation of source leaf pairs
with full meet 1 is synchronised, the actual chosen map satisfies
EVERY diary-pre-embedding condition. No assumption about order
preservation of F or meet preservation through skipped target
enumeration levels occurs in the statement. -/
theorem chosenPreembedding_spec_of_relative_orientation
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (hFleaf : ∀ t, IsLeaf K (F t))
    (D : RoleDiary H) (E : RoleDiary K)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (hrelative :
      ∀ a b c d : Nat,
        a < b → c < d →
        IsLeaf H a → IsLeaf H b →
        IsLeaf H c → IsLeaf H d →
        H.twoMeetLevel a b c d = 1 →
        ((LexEarlier H a b ↔ LexEarlier H c d) ↔
          (LexEarlier K (stabilisedSource G K F ψ a)
              (stabilisedSource G K F ψ b) ↔
           LexEarlier K (stabilisedSource G K F ψ c)
              (stabilisedSource G K F ψ d)))) :
    DiaryPreembeddingSpec H K
      (D.chosenPreembedding G K F ψ) := by
  let φ := stabilisedSource G K F ψ
  have hImageLeaf (u : Nat) : IsLeaf K (φ u) :=
    stabilisedSource_isLeaf_of_outer_leaves G K F hFleaf ψ u
  have hmarker :
      ∀ a b c d : Nat,
        a < b → c < d →
        IsLeaf H a → IsLeaf H b →
        IsLeaf H c → IsLeaf H d →
        H.twoMeetLevel a b c d = 1 →
        K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) = 1 := by
    intro a b c d hab hcd ha hb hc hd hMeet
    exact D.markerOne_pairMeet_transfer_of_relative_orientation
      E φ a b c d hab hcd ha hb hc hd
      (hImageLeaf a) (hImageLeaf b)
      (hImageLeaf c) (hImageLeaf d)
      hMeet (hrelative a b c d hab hcd ha hb hc hd hMeet)
  refine {
    strictMono := D.chosenPreembedding_strictMono G K F ψ hψ
    marker_zero := D.chosenPreembedding_zero G K F ψ
    marker_one := D.chosenPreembedding_one G K F ψ
    marker_two := D.chosenPreembedding_two G K F ψ
    leaf_role := ?_
    one_split_role := ?_
    two_split_role := ?_
    leaf_edge_iff := ?_
    leaf_one_meet := ?_
    leaf_two_meet := ?_
  }
  · intro u hu
    exact D.chosenPreembedding_preserves_leaf_role
      G K F hFleaf ψ u hu
  · intro i hi
    exact D.chosenPreembedding_preserves_oneSplit_role
      G K F hFleaf E ψ i hi
  · intro i hi
    exact D.chosenPreembedding_preserves_twoSplit_role
      G K F hFleaf E ψ hψ i hi
  · intro a b c hab hbc ha hb hc
    exact D.chosenPreembedding_leaf_edge_iff
      G K F ψ a b c hab hbc ha hb hc
  · intro u v hu hv
    rw [D.chosenPreembedding_leaf G K F ψ u hu,
        D.chosenPreembedding_leaf G K F ψ v hv]
    exact D.chosenPreembedding_preserves_leaf_oneMeet
      G K F ψ hψ u v hu hv
  · intro a b c d hab hcd ha hb hc hd
    rw [D.chosenPreembedding_leaf G K F ψ a ha,
        D.chosenPreembedding_leaf G K F ψ b hb,
        D.chosenPreembedding_leaf G K F ψ c hc,
        D.chosenPreembedding_leaf G K F ψ d hd]
    exact D.chosenPreembedding_preserves_all_leaf_twoMeets_of_markerOne
      G K F ψ hψ hmarker a b c d hab hcd ha hb hc hd

/-- The conditional complete pre-embedding property together
with the REQUIRED inclusion of the source leaf images in the
original unordered embedding F[G]. -/
theorem chosenPreembedding_spec_and_leaf_range_of_relative_orientation
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (hFleaf : ∀ t, IsLeaf K (F t))
    (D : RoleDiary H) (E : RoleDiary K)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (hrelative :
      ∀ a b c d : Nat,
        a < b → c < d →
        IsLeaf H a → IsLeaf H b →
        IsLeaf H c → IsLeaf H d →
        H.twoMeetLevel a b c d = 1 →
        ((LexEarlier H a b ↔ LexEarlier H c d) ↔
          (LexEarlier K (stabilisedSource G K F ψ a)
              (stabilisedSource G K F ψ b) ↔
           LexEarlier K (stabilisedSource G K F ψ c)
              (stabilisedSource G K F ψ d)))) :
    DiaryPreembeddingSpec H K
        (D.chosenPreembedding G K F ψ) ∧
      ∀ u, IsLeaf H u →
        ∃ t, D.chosenPreembedding G K F ψ u = F t := by
  exact ⟨D.chosenPreembedding_spec_of_relative_orientation
      G K F hFleaf E ψ hψ hrelative,
    D.chosenPreembedding_leaf_range_subset G K F ψ⟩

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
