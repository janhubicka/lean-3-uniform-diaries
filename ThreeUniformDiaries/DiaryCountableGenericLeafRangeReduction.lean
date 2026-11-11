import ThreeUniformDiaries.DiaryCertifiedFusionStrongOutput
import ThreeUniformDiaries.DiaryFiniteUniversalLeafRange

/-!
# Track C: countable universal-range unavoidability reduces to generic ranges

English-first proof and adversarial quantifier audit:
  janhubicka/3-uniform-diaries PR #290

The finite-source reduction from arbitrary countably universal U to an
unordered induced enumerated generic G was already checked in
DiaryFiniteUniversalLeafRange. This module records the COUNTABLE-output
reduction with the actual strong diary certificate.

The target claim is NOT proved: FullGenericLeafRangeUnavoidable is an
explicit hypothesis. Composition of an unordered induced generic copy
G -> U with a prescribed unordered F:U -> K yields FG:G -> K.
A full strong diary embedding with leaves in FG[G] has its leaves
automatically in the original F[U].

The reduction does NOT assert bounded persistence of every old stage
in the larger range F[U] and does not construct a relative successor.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The still-unproved countable diary unavoidability statement when
the prescribed target leaf range is an actual unordered induced
enumerated generic 3-uniform hypergraph. The output includes the
SAME genuine marker/role preembedding certificate and TypeRespecting
induced ordered embedding, not just a leaf-only hypergraph copy. -/
def FullGenericLeafRangeUnavoidable
    (H K : Ordered3Graph Nat) (G : GenericEnumerated3Graph) : Prop :=
  ∀ (F : Ordered3Graph.UnorderedEmbedding G.graph K),
    (∀ t : Nat, IsLeaf K (F t)) →
    ∃ e : Ordered3Graph.Embedding H K,
      DiaryPreembeddingSpec H K (fun u : Nat => e u) ∧
      e.TypeRespecting ∧
      (∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t)

/-- The printed countable unavoidability target for an arbitrary
countably universal U, retaining the same FULL diary output and
the ORIGINAL prescribed F[U] leaf range. -/
def FullUniversalLeafRangeUnavoidable
    (H K : Ordered3Graph Nat) : Prop :=
  ∀ (U : Ordered3Graph Nat),
    Ordered3Graph.CountablyUniversal U →
    ∀ (F : Ordered3Graph.UnorderedEmbedding U K),
      (∀ t : Nat, IsLeaf K (F t)) →
      ∃ e : Ordered3Graph.Embedding H K,
        DiaryPreembeddingSpec H K (fun u : Nat => e u) ∧
        e.TypeRespecting ∧
        (∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t)

/-- It is mathematically sufficient to prove the still-open
countable generic-range theorem. For every original universal
range F[U], compose F with any induced unordered copy i:G -> U;
then apply the generic theorem, preserving EXACTLY the same
embedding, diary preembedding certificate and full TypeRespecting
property. Only the leaf-range membership witness is composed. -/
theorem fullUniversalLeafRangeUnavoidable_of_fullGenericLeafRangeUnavoidable
    (H K : Ordered3Graph Nat) (G : GenericEnumerated3Graph)
    (hGeneric : FullGenericLeafRangeUnavoidable H K G) :
    FullUniversalLeafRangeUnavoidable H K := by
  classical
  intro U hUniversal F hLeaves
  let i : Ordered3Graph.UnorderedEmbedding G.graph U :=
    Classical.choice (hUniversal G.graph)
  let FG : Ordered3Graph.UnorderedEmbedding G.graph K := F.comp i
  have hFGLeaves : ∀ t : Nat, IsLeaf K (FG t) := by
    intro t
    exact hLeaves (i t)
  obtain ⟨e, hSpec, hType, hRange⟩ := hGeneric FG hFGLeaves
  refine ⟨e, hSpec, hType, ?_⟩
  intro u hu
  obtain ⟨t, ht⟩ := hRange u hu
  change e u = F (i t) at ht
  exact ⟨i t, ht⟩

end DiaryLeafPriority
end ThreeUniformDiaries
