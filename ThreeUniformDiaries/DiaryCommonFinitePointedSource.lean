import ThreeUniformDiaries.DiaryFusedEnvelopeColours

/-!
# The abstract I3 stabilisation lemma for common finite ATR pointed sources

The manuscript's condition (I3) applies to two ordered vertex pairs
whose minimal pointed envelopes are equal as enumerated hypergraphs
and whose canonical inclusions are ATR-admissible. The genuinely
finite version of that premise is a SHARED native `EnumNode` source
together with two prefix-fixing finite ATR embedding codes and the
identification of their last two vertex images with the requested
endpoints.

This module isolates exactly that semantic premise, without making
any choices of infinite extensions and without replacing the
abstract `Env` object by an unjustified global embedding.

The previously checked fused colour theorem gives condition (I3)
directly under this common-source premise: complete target 2-type
agreement and lexicographic orientation agreement at the correct
predecessor image target cut. Concrete diary two- or three-tail
constructions produce such certificates in separate modules.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- Two ordered pairs of generic vertices are represented by two
genuine prefix-fixed finite ATR embeddings of ONE native small
pointed source, with the pairs occupying its distinguished last
two source positions. The two codes need not share any image
vertices beyond the fixed protected prefix. -/
structure CommonFinitePointedSource
    (G : GenericEnumerated3Graph)
    (i a b c d : Nat) where
  source : ProtectedSource i
  source_small : source ∈ smallSourceUniverse i
  first : source.Code G
  second : source.Code G
  first_fixes_prefix : source.FixesPrefix G first
  second_fixes_prefix : source.FixesPrefix G second
  first_left : first.image source.penultimateIndex = a
  first_right : first.image source.lastIndex = b
  second_left : second.image source.penultimateIndex = c
  second_right : second.image source.lastIndex = d

/-- Exact generic native finite representation of the manuscript's
"same ATR-admissible pointed envelope" premise. The carrier and
finite source shape are data in the certificate, but the relation
between the vertex pairs is a proposition. -/
def SameFinitePointedSource
    (G : GenericEnumerated3Graph)
    (i a b c d : Nat) : Prop :=
  Nonempty (CommonFinitePointedSource G i a b c d)

/-- The complete I3 conclusion follows for ANY two ordered pairs
represented by the same genuine finite ATR pointed source. The
outer map is arbitrary injective, not assumed order-preserving.

This is the type-stabilisation lemma's pair assertion in the exact
finite-source interface. To instantiate the original manuscript's
`Env` notation one must check that its canonical selected
envelopes yield such a common-source certificate. -/
theorem orderedDiaryFusion_I3_of_common_finite_source
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F)
    (i : Nat) (hi : 0 < i)
    (a b c d : Nat)
    (hcommon : SameFinitePointedSource G i a b c d) :
    let g := orderedDiaryFusion G K F hF
    let N := F (g (i-1)) + 1
    K.SameTwoTypeBelow N
      (F (g a)) (F (g b))
      (F (g c)) (F (g d)) ∧
    (DiaryLeafPriority.LexEarlier K (F (g a)) (F (g b)) ↔
      DiaryLeafPriority.LexEarlier K (F (g c)) (F (g d))) := by
  obtain ⟨S⟩ := hcommon
  have h := orderedDiaryFusion_pairType_orientation
    G K F hF i hi S.source S.source_small
      S.first S.second S.first_fixes_prefix
      S.second_fixes_prefix
  simpa only [S.first_left, S.first_right,
    S.second_left, S.second_right] using h

end ATRFiniteDecoder
end ThreeUniformDiaries
