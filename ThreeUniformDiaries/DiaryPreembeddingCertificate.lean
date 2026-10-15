import ThreeUniformDiaries.DiaryChosenPreembeddingRoles
import ThreeUniformDiaries.DiaryChosenLeafOneMeets
import ThreeUniformDiaries.DiaryChosenLeafPairMeetCases
import ThreeUniformDiaries.DiaryMarkerOnePairReduction
import ThreeUniformDiaries.DiaryChosenLeafImageRange

/-!
# The complete diary pre-embedding conditional only on global orientation

This is the precise final interface for the manuscript's
pre-embedding lemma. A diary pre-embedding fixes markers 0,1,2,
is strictly increasing, preserves the three vertex roles, is an
induced embedding on the leaf part, and preserves the actual
singleton and full pair-type meets of leaf sets.

The verified witness-chosen map already satisfies all these
conditions EXCEPT for the global marker-one orientation step.
The sole additional mathematical premise here says that, for
every pair of ordered source leaf pairs, their lexicographic
orientations agree with each other exactly when their image
orientations agree with each other. This allows either uniform
preservation OR uniform reversal of all orientations.

From this relative-orientation premise the complete source
diary V/E/S axioms identify marker-one full pair meets in the
target. The other two full-pair-meet cases were independently
proved (actual two-split I3 and capped singleton argument).
The original external embedding is UNORDERED and takes the
generic graph into target diary leaves.

This theorem deliberately does NOT claim the orientation
premise. The outstanding cut-zero three-leaf-gadget
amalgamation must establish it; once that is done the present
certificate is the complete lower-bound pre-embedding.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- The manuscript's diary pre-embedding properties, expressed on
the actual ordered leaf tuples and edge-derived type meets.
There is no fictitious preservation of meets involving arbitrary
split vertices. -/
structure DiaryPreembeddingCertificate
    (H K : Ordered3Graph Nat) (f : Nat → Nat) : Prop where
  strictMono : StrictMono f
  marker_zero : f 0 = 0
  marker_one : f 1 = 1
  marker_two : f 2 = 2
  leaf_role : ∀ u, IsLeaf H u → IsLeaf K (f u)
  oneSplit_role : ∀ u, IsOneSplit H u → IsOneSplit K (f u)
  twoSplit_role : ∀ u, IsTwoSplit H u → IsTwoSplit K (f u)
  leaf_edge_iff :
    ∀ a b c, a < b → b < c →
      IsLeaf H a → IsLeaf H b → IsLeaf H c →
      (H.edge a b c ↔ K.edge (f a) (f b) (f c))
  leaf_one_meet :
    ∀ u v, IsLeaf H u → IsLeaf H v →
      K.oneMeetLevel (f u) (f v) = f (H.oneMeetLevel u v)
  leaf_two_meet :
    ∀ a b c d, a < b → c < d →
      IsLeaf H a → IsLeaf H b → IsLeaf H c → IsLeaf H d →
      K.twoMeetLevel (f a) (f b) (f c) (f d) =
        f (H.twoMeetLevel a b c d)

namespace RoleDiary

open Ordered3Graph.UnorderedEmbedding

variable {H : Ordered3Graph Nat}

/-- The actual witness-chosen diary map is a full
pre-embedding, with its leaf image inside the original outer
embedding F, as soon as the still-open RELATIVE ORIENTATION
conclusion is supplied.

Everything else is discharged by the verified concrete
V/E/S split witnesses, genuine gappy I2/I3 fusion, capped
leaf-pair argument, role analysis and induced leaf edges.
No artificial equality of skipped-level types is assumed. -/
theorem chosenPreembedding_certificate_of_relative_orientation
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (hFleaf : ∀ t, IsLeaf K (F t))
    (D : RoleDiary H) (E : RoleDiary K)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (hrelative :
      ∀ a b c d : Nat, a < b → c < d →
        IsLeaf H a → IsLeaf H b →
        IsLeaf H c → IsLeaf H d →
        ((LexEarlier H a b ↔ LexEarlier H c d) ↔
         (LexEarlier K (stabilisedSource G K F ψ a)
           (stabilisedSource G K F ψ b) ↔
          LexEarlier K (stabilisedSource G K F ψ c)
           (stabilisedSource G K F ψ d)))) :
    DiaryPreembeddingCertificate H K
      (D.chosenPreembedding G K F ψ) ∧
    (∀ u, IsLeaf H u →
      ∃ t, D.chosenPreembedding G K F ψ u = F t) := by
  let φ := stabilisedSource G K F ψ
  obtain ⟨hmono, hLeaves, hOneRole, hTwoRole, hEdges⟩ :=
    D.chosenPreembedding_roles_and_leaf_edges
      G K F hFleaf E ψ hψ
  have hMarker :
      ∀ a b c d : Nat,
        a < b → c < d →
        IsLeaf H a → IsLeaf H b →
        IsLeaf H c → IsLeaf H d →
        H.twoMeetLevel a b c d = 1 →
        K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) = 1 := by
    intro a b c d hab hcd ha hb hc hd hMeet
    have haT : IsLeaf K (φ a) :=
      stabilisedSource_isLeaf_of_outer_leaves G K F hFleaf ψ a
    have hbT : IsLeaf K (φ b) :=
      stabilisedSource_isLeaf_of_outer_leaves G K F hFleaf ψ b
    have hcT : IsLeaf K (φ c) :=
      stabilisedSource_isLeaf_of_outer_leaves G K F hFleaf ψ c
    have hdT : IsLeaf K (φ d) :=
      stabilisedSource_isLeaf_of_outer_leaves G K F hFleaf ψ d
    exact D.markerOne_pairMeet_transfer_of_relative_orientation
      E φ a b c d hab hcd ha hb hc hd
      haT hbT hcT hdT hMeet
      (hrelative a b c d hab hcd ha hb hc hd)
  refine ⟨{
    strictMono := hmono
    marker_zero := D.chosenPreembedding_zero G K F ψ
    marker_one := D.chosenPreembedding_one G K F ψ
    marker_two := D.chosenPreembedding_two G K F ψ
    leaf_role := hLeaves
    oneSplit_role := hOneRole
    twoSplit_role := hTwoRole
    leaf_edge_iff := hEdges
    leaf_one_meet := ?_
    leaf_two_meet := ?_
  }, ?_⟩
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
      G K F ψ hψ hMarker a b c d hab hcd ha hb hc hd
  · exact D.chosenPreembedding_leaf_range_subset G K F ψ

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
