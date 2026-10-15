import ThreeUniformDiaries.UniversalAuxBranchEmbedding
import ThreeUniformDiaries.DiaryFiveVertexUnorderedApplication

/-!
# Every ordered 3-hypergraph has a type-respecting generic copy fixing 0 and 1

The original pre-embedding proof chooses the diary-to-generic map
with empty protected prefix, but the verified indexed K_I
construction actually gives a stronger and useful interface.

The induced hypergraph on the first TWO vertices has no
3-uniform edges in ANY enumerated hypergraph. Therefore the
source and generic target initial segments of size 2 agree,
regardless of their other edge predicates. Applying the
already proved universal fixed-prefix auxiliary-type
embedding theorem yields a genuine increasing induced and
type-respecting embedding of the entire source into the
generic hypergraph fixing vertices 0 and 1.

This avoids an unnecessary prefix-shift problem when
representing a diary's source one-split marker edges
{0,1,m} and {0,m,u} as native finite ATR source shapes
at protected cut 2. It works for every source ordered
3-hypergraph, not just diaries or the five-vertex gadget.

No new Ramsey theorem, finite source existence axiom, or
global orientation synchronisation is introduced.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- All enumerated 3-uniform hypergraphs have the same induced
two-vertex initial segment, since there are no increasing
triples in that segment. -/
theorem initialSegment_two_eq
    (H K : Ordered3Graph Nat) :
    H.initialSegment 2 = K.initialSegment 2 := by
  apply EnumNode.ext_triples
  funext a b c
  have hbad : ¬ (a < b ∧ b < c ∧ c < 2) := by omega
  calc
    (H.initialSegment 2).triple a b c = false :=
      (H.initialSegment 2).support a b c hbad
    _ = (K.initialSegment 2).triple a b c :=
      ((K.initialSegment 2).support a b c hbad).symm

/-- The universal fixed-prefix generic embedding theorem
produces a type-respecting induced copy of ANY ordered
source 3-hypergraph fixing its first two vertices. The
embedding may skip all later target enumeration levels. -/
theorem exists_typeRespecting_embedding_fix_two
    (G : GenericEnumerated3Graph) (H : Ordered3Graph Nat) :
    ∃ ψ : Embedding H G.graph,
      ψ.TypeRespecting ∧ ψ 0 = 0 ∧ ψ 1 = 1 := by
  let I : EnumNode 2 := G.graph.initialSegment 2
  obtain ⟨E, phi, hproperty⟩ :=
    exists_universal_fixedAuxEmbedding G I (by omega) rfl
  have hI : H.initialSegment 2 = I :=
    initialSegment_two_eq H G.graph
  obtain ⟨ψ, _, hfix, haux⟩ :=
    hproperty.2.2.2 H hI
  exact ⟨ψ, haux.typeRespecting,
    hfix 0 (by omega), hfix 1 (by omega)⟩

end ATRFiniteDecoder
end ThreeUniformDiaries
