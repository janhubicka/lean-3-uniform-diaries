import ThreeUniformDiaries.DiaryCanonicalMarkedNestedReindex

/-!
# Reindexing nested finite supports preserves the exact induced graph

For any finite T ⊆ S of natural-number vertices, sorting the
rank image of T inside S recovers the same vertex sequence
as sorting T directly. Hence doing two consecutive canonical
induced finite-graph restrictions is literally the same
as restricting once to T, INCLUDING nonedges.

The proof is pure finite-set/order bookkeeping and does not
invoke RoleDiary axioms or global type-respecting compression.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Two canonical finite-induced restrictions are literally
equal as ordered ternary graphs, provided the smaller support
T is contained in the larger support S. -/
theorem finiteSupportGraph_nested_rank_eq
    (K : Ordered3Graph Nat)
    (S T : Finset Nat) (hTS : T ⊆ S) :
    finiteSupportGraph
        (finiteSupportGraph K S)
        (T.image (finiteSupportRank S)) =
      finiteSupportGraph K T := by
  classical
  let V : Finset Nat := T.image (finiteSupportRank S)
  let H : Ordered3Graph Nat := finiteSupportGraph K S
  have hCard : V.card = T.card :=
    finiteSupportRank_image_card S T hTS
  have hIndex (i : Nat) (hi : i < T.card) :
      finiteSupportIndex S (finiteSupportIndex V i) =
        finiteSupportIndex T i := by
    have h := finiteSupportIndex_nested_rank_image S T hTS i hi
    change finiteSupportIndex V i =
      finiteSupportRank S (finiteSupportIndex T i) at h
    rw [h]
    exact (finiteSupportRank_spec S _
      (hTS (finiteSupportIndex_mem T i hi))).2
  have hInside (i : Nat) (hi : i < T.card) :
      finiteSupportIndex V i < S.card := by
    have h := finiteSupportIndex_nested_rank_image S T hTS i hi
    change finiteSupportIndex V i =
      finiteSupportRank S (finiteSupportIndex T i) at h
    rw [h]
    exact (finiteSupportRank_spec S _
      (hTS (finiteSupportIndex_mem T i hi))).1
  have hOrderedEdge (a b c : Nat)
      (hab : a < b) (hbc : b < c) (hc : c < T.card) :
      (finiteSupportGraph H V).edge a b c ↔
        (finiteSupportGraph K T).edge a b c := by
    have hvc : c < V.card := by rw [hCard]; exact hc
    have hb : b < T.card := by omega
    have ha : a < T.card := by omega
    have hvb : b < V.card := by omega
    have hVab : finiteSupportIndex V a < finiteSupportIndex V b :=
      finiteSupportIndex_strictMono V a b hab hvb
    have hVbc : finiteSupportIndex V b < finiteSupportIndex V c :=
      finiteSupportIndex_strictMono V b c hbc hvc
    have hInner :
        H.edge (finiteSupportIndex V a)
               (finiteSupportIndex V b)
               (finiteSupportIndex V c) ↔
        K.edge (finiteSupportIndex T a)
               (finiteSupportIndex T b)
               (finiteSupportIndex T c) := by
      have h := finiteSupportGraph_edge_iff K S
        (finiteSupportIndex V a)
        (finiteSupportIndex V b)
        (finiteSupportIndex V c)
        hVab hVbc (hInside c hc)
      rw [hIndex a ha, hIndex b hb, hIndex c hc] at h
      exact h
    calc
      (finiteSupportGraph H V).edge a b c ↔
          H.edge (finiteSupportIndex V a)
            (finiteSupportIndex V b)
            (finiteSupportIndex V c) :=
        finiteSupportGraph_edge_iff H V a b c hab hbc hvc
      _ ↔ K.edge (finiteSupportIndex T a)
          (finiteSupportIndex T b) (finiteSupportIndex T c) := hInner
      _ ↔ (finiteSupportGraph K T).edge a b c :=
        (finiteSupportGraph_edge_iff K T a b c hab hbc hc).symm
  have hEdges :
      (finiteSupportGraph H V).edge =
        (finiteSupportGraph K T).edge := by
    funext a b c
    apply propext
    constructor
    · intro he
      obtain ⟨hab,hbc,hvc⟩ :=
        finiteSupportGraph_edge_ordered H V a b c he
      have hc : c < T.card := by rw [hCard] at hvc; exact hvc
      exact (hOrderedEdge a b c hab hbc hc).mp he
    · intro he
      obtain ⟨hab,hbc,hc⟩ :=
        finiteSupportGraph_edge_ordered K T a b c he
      exact (hOrderedEdge a b c hab hbc hc).mpr he
  change (Ordered3Graph.mk (finiteSupportGraph H V).edge) =
    (Ordered3Graph.mk (finiteSupportGraph K T).edge)
  exact congrArg Ordered3Graph.mk hEdges

/-- The selected vertex has the same canonical finite rank
whether we enumerate it directly inside T or first take its
rank in S and then enumerate the image of T. -/
theorem finiteSupportRank_nested_rank_image
    (S T : Finset Nat) (hTS : T ⊆ S)
    (x : Nat) (hx : x ∈ T) :
    finiteSupportRank (T.image (finiteSupportRank S))
        (finiteSupportRank S x) =
      finiteSupportRank T x := by
  classical
  let V : Finset Nat := T.image (finiteSupportRank S)
  have hCard : V.card = T.card :=
    finiteSupportRank_image_card S T hTS
  have hRankT := finiteSupportRank_spec T x hx
  have hiV : finiteSupportRank T x < V.card := by
    rw [hCard]
    exact hRankT.1
  have hIndex := finiteSupportIndex_nested_rank_image
    S T hTS (finiteSupportRank T x) hRankT.1
  change finiteSupportIndex V (finiteSupportRank T x) =
    finiteSupportRank S (finiteSupportIndex T (finiteSupportRank T x))
      at hIndex
  rw [hRankT.2] at hIndex
  have hRankV := finiteSupportRank_of_index
    V (finiteSupportRank T x) hiV
  rw [hIndex] at hRankV
  exact hRankV

end DiaryLeafPriority
end ThreeUniformDiaries
