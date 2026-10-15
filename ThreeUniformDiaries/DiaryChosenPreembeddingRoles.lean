import ThreeUniformDiaries.DiaryChosenPreembedding

/-!
# The chosen diary pre-embedding preserves all vertex roles

A lower-bound application starts with an arbitrary embedding of the
UNORDERED generic hypergraph into the leaf-induced part of a target
diary. Thus the original outer embedding need not be increasing, but
its entire image consists of target LEAVES.

The verified fusion produces a genuinely increasing induced embedding
of the source diary into the target hypergraph. Sending leaves by this
map and splits by the singleton/full-pair type meets of their chosen
V1/V2 witnesses preserves all three diary roles:

* Leaves remain leaves because every value of the outer embedding
  already has that role.
* A one-split becomes a one-split by target S1, since its two
  chosen witness leaves are distinct.
* A two-split becomes a two-split by target S2. The proved interval
  excludes the exceptional marker-1 case, and the upper interval
  bound excludes a capped pair meet.

The leaf-induced edge relation is preserved and reflected literally,
as the total chosen map agrees with the fused ordered embedding on
leaves. There is no claim here about all singleton/pair meets,
lexicographic orientation or marker-edge preservation.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph
open Ordered3Graph.UnorderedEmbedding

variable {H : Ordered3Graph Nat}

/-- Every image of the stabilised source embedding is a target
leaf when the original, potentially unordered, outer map has
its image in the leaf set of the target diary. -/
theorem stabilisedSource_isLeaf_of_outer_leaves
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (hFleaf : ∀ t, IsLeaf K (F t))
    (ψ : Embedding H G.graph) (t : Nat) :
    IsLeaf K (stabilisedSource G K F ψ t) := by
  change IsLeaf K (stabilisedOrdered G K F (ψ t))
  rw [stabilisedOrdered_apply]
  exact hFleaf _

/-- The one-split image of the chosen candidate is a genuine
target one-split. Target S1 only needs its two image witnesses
to be different leaves; the source zero-marker disagreement
proves they are different. -/
theorem chosenPreembedding_preserves_oneSplit_role
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (hFleaf : ∀ t, IsLeaf K (F t))
    (D : RoleDiary H) (E : RoleDiary K)
    (ψ : Embedding H G.graph)
    (i : Nat) (hi : IsOneSplit H i) :
    IsOneSplit K (D.chosenPreembedding G K F ψ i) := by
  let φ := stabilisedSource G K F ψ
  let w := D.chosenOneSplitWitness i hi
  have hOpp : ¬ (H.edge 0 i w.u ↔ H.edge 0 i w.v) :=
    D.oneSplit_witness_opposite_marker
      i w.u w.v hi w.hu w.hv w.hiu w.hiv w.meet_eq
  have hneq : w.u ≠ w.v := by
    intro h
    apply hOpp
    rw [h]
  have hneqT : φ w.u ≠ φ w.v := by
    intro h
    exact hneq (φ.strictMono.injective h)
  have huT : IsLeaf K (φ w.u) :=
    stabilisedSource_isLeaf_of_outer_leaves G K F hFleaf ψ w.u
  have hvT : IsLeaf K (φ w.v) :=
    stabilisedSource_isLeaf_of_outer_leaves G K F hFleaf ψ w.v
  rw [D.chosenPreembedding_oneSplit G K F ψ i hi]
  change IsOneSplit K (K.oneMeetLevel (φ w.u) (φ w.v))
  exact E.singleton_meets (φ w.u) (φ w.v) huT hvT hneqT

/-- The two-split image of the candidate is a genuine two-split.
The target S2 trichotomy has a capped case, a marker-1 case and
the desired role; the strict predecessor interval excludes the
marker, and the upper interval excludes the cap. -/
theorem chosenPreembedding_preserves_twoSplit_role
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (hFleaf : ∀ t, IsLeaf K (F t))
    (D : RoleDiary H) (E : RoleDiary K)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (i : Nat) (hi : IsTwoSplit H i) :
    IsTwoSplit K (D.chosenPreembedding G K F ψ i) := by
  let φ := stabilisedSource G K F ψ
  let w := D.chosenTwoSplitWitness i hi
  have hAB : φ w.a < φ w.b := φ.strictMono w.hab
  have hCD : φ w.c < φ w.d := φ.strictMono w.hcd
  have hA : IsLeaf K (φ w.a) :=
    stabilisedSource_isLeaf_of_outer_leaves G K F hFleaf ψ w.a
  have hB : IsLeaf K (φ w.b) :=
    stabilisedSource_isLeaf_of_outer_leaves G K F hFleaf ψ w.b
  have hC : IsLeaf K (φ w.c) :=
    stabilisedSource_isLeaf_of_outer_leaves G K F hFleaf ψ w.c
  have hD : IsLeaf K (φ w.d) :=
    stabilisedSource_isLeaf_of_outer_leaves G K F hFleaf ψ w.d
  have hPlacement := D.twoSplitTargetImage_interval G K F ψ hψ i hi
  change φ (i-1) <
      K.twoMeetLevel (φ w.a) (φ w.b) (φ w.c) (φ w.d) ∧
    K.twoMeetLevel (φ w.a) (φ w.b) (φ w.c) (φ w.d) ≤ φ i
    at hPlacement
  have hNonMarker : 1 < φ (i-1) := by
    have hID := strictMono_nat_ge_id φ φ.strictMono (i-1)
    have hb := hi.1
    omega
  have hAboveCap : φ i < min (φ w.a) (φ w.c) :=
    lt_min (φ.strictMono w.hia) (φ.strictMono w.hic)
  have hrole : IsTwoSplit K
      (K.twoMeetLevel (φ w.a) (φ w.b) (φ w.c) (φ w.d)) := by
    rcases E.pair_meets
      (φ w.a) (φ w.b) (φ w.c) (φ w.d)
      hAB hCD hA hB hC hD with hCap | hMarker | hTwo
    · omega
    · omega
    · exact hTwo
  rw [D.chosenPreembedding_twoSplit G K F ψ i hi]
  exact hrole

/-- Every source leaf remains a target leaf. The restriction of
the chosen map to leaves is literally the stabilised copy. -/
theorem chosenPreembedding_preserves_leaf_role
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (hFleaf : ∀ t, IsLeaf K (F t))
    (D : RoleDiary H) (ψ : Embedding H G.graph)
    (i : Nat) (hi : IsLeaf H i) :
    IsLeaf K (D.chosenPreembedding G K F ψ i) := by
  rw [D.chosenPreembedding_leaf G K F ψ i hi]
  exact stabilisedSource_isLeaf_of_outer_leaves G K F hFleaf ψ i

/-- The chosen total map preserves AND reflects the induced edge
relation on strictly increasing triples of source leaves, because
it agrees with the fully checked ordered induced embedding there. -/
theorem chosenPreembedding_leaf_edge_iff
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H) (ψ : Embedding H G.graph)
    (a b c : Nat) (hab : a < b) (hbc : b < c)
    (ha : IsLeaf H a) (hb : IsLeaf H b) (hc : IsLeaf H c) :
    H.edge a b c ↔
      K.edge (D.chosenPreembedding G K F ψ a)
        (D.chosenPreembedding G K F ψ b)
        (D.chosenPreembedding G K F ψ c) := by
  rw [D.chosenPreembedding_leaf G K F ψ a ha,
      D.chosenPreembedding_leaf G K F ψ b hb,
      D.chosenPreembedding_leaf G K F ψ c hc]
  exact (stabilisedSource G K F ψ).edge_iff hab hbc

/-- Package the three target roles, strict monotonicity, and
literal leaf-induced subhypergraph embedding in the one
candidate constructed from genuine source V1/V2 witnesses. -/
theorem chosenPreembedding_roles_and_leaf_edges
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (hFleaf : ∀ t, IsLeaf K (F t))
    (D : RoleDiary H) (E : RoleDiary K)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting) :
    StrictMono (D.chosenPreembedding G K F ψ) ∧
    (∀ i, IsLeaf H i →
      IsLeaf K (D.chosenPreembedding G K F ψ i)) ∧
    (∀ i, IsOneSplit H i →
      IsOneSplit K (D.chosenPreembedding G K F ψ i)) ∧
    (∀ i, IsTwoSplit H i →
      IsTwoSplit K (D.chosenPreembedding G K F ψ i)) ∧
    (∀ a b c, a < b → b < c →
      IsLeaf H a → IsLeaf H b → IsLeaf H c →
      (H.edge a b c ↔
        K.edge (D.chosenPreembedding G K F ψ a)
          (D.chosenPreembedding G K F ψ b)
          (D.chosenPreembedding G K F ψ c))) := by
  refine ⟨D.chosenPreembedding_strictMono G K F ψ hψ, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact D.chosenPreembedding_preserves_leaf_role
      G K F hFleaf ψ i hi
  · intro i hi
    exact D.chosenPreembedding_preserves_oneSplit_role
      G K F hFleaf E ψ i hi
  · intro i hi
    exact D.chosenPreembedding_preserves_twoSplit_role
      G K F hFleaf E ψ hψ i hi
  · intro a b c hab hbc ha hb hc
    exact D.chosenPreembedding_leaf_edge_iff
      G K F ψ a b c hab hbc ha hb hc

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
