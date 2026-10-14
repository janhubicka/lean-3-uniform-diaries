import ThreeUniformDiaries.DiaryCompleteNativeStabilisation

/-!
# Unordered hypergraph embeddings in the diary lower bound

The manuscript starts with an arbitrary induced embedding F of the
underlying 3-uniform hypergraph, *not* an order-preserving embedding.
The existing `Ordered3Graph.Embedding` API is strictly increasing,
so using it for F would make conclusion (I1) vacuous.

An unordered hyperedge is defined by first arranging its three
distinct indices in increasing order. An unordered embedding is an
injective map preserving and reflecting that predicate.

Once a suitable aux-type-respecting generic self-embedding g has
made F ∘ g strictly increasing (by the verified I1 theorem),
their composite becomes a genuine order-preserving induced
embedding. This is the exact bridge required to transport the
five-vertex orientation gadget into an arbitrary target.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- The symmetric, irreflexive underlying 3-hyperedge relation of
an enumerated 3-graph. Each disjunct explicitly checks the
strictly increasing order of the three chosen vertices, so
non-increasing entries of the raw edge predicate are irrelevant. -/
def unorderedEdge (H : Ordered3Graph Nat) (a b c : Nat) : Prop :=
  (a < b ∧ b < c ∧ H.edge a b c) ∨
  (a < c ∧ c < b ∧ H.edge a c b) ∨
  (b < a ∧ a < c ∧ H.edge b a c) ∨
  (b < c ∧ c < a ∧ H.edge b c a) ∨
  (c < a ∧ a < b ∧ H.edge c a b) ∨
  (c < b ∧ b < a ∧ H.edge c b a)

/-- For an already increasing triple, the symmetric underlying
edge condition is definitionally equivalent to the recorded
ordered edge predicate. -/
theorem unorderedEdge_iff_of_lt
    (H : Ordered3Graph Nat) (a b c : Nat)
    (hab : a < b) (hbc : b < c) :
    H.unorderedEdge a b c ↔ H.edge a b c := by
  have hac : a < c := lt_trans hab hbc
  have hba : ¬ b < a := not_lt_of_ge hab.le
  have hca : ¬ c < a := not_lt_of_ge hac.le
  have hcb : ¬ c < b := not_lt_of_ge hbc.le
  simp [unorderedEdge, hab, hbc, hac, hba, hca, hcb]

/-- An induced embedding of the underlying *unordered* 3-graph.
No monotonicity of the vertex map is required, only injectivity.
Every source increasing triple is tested using the symmetric
unordered edge relation in the target. -/
structure UnorderedEmbedding (H K : Ordered3Graph Nat) where
  toFun : Nat → Nat
  injective : Function.Injective toFun
  edge_iff :
    ∀ a b c : Nat, a < b → b < c →
      (H.unorderedEdge a b c ↔
       K.unorderedEdge (toFun a) (toFun b) (toFun c))

namespace UnorderedEmbedding

variable {H G K : Ordered3Graph Nat}

instance : CoeFun (UnorderedEmbedding G K) (fun _ => Nat → Nat) :=
  ⟨UnorderedEmbedding.toFun⟩

/-- Once the composite F ∘ g is increasing, it reflects the
ordered edge relation on every increasing source triple. -/
theorem composed_ordered_edges
    (F : UnorderedEmbedding G K)
    (g : Embedding G G)
    (hOrder : StrictMono (fun t => F (g t)))
    (a b c : Nat) (hab : a < b) (hbc : b < c) :
    G.edge a b c ↔ K.edge (F (g a)) (F (g b)) (F (g c)) := by
  calc
    G.edge a b c ↔ G.edge (g a) (g b) (g c) :=
      g.edge_iff hab hbc
    _ ↔ G.unorderedEdge (g a) (g b) (g c) :=
      (G.unorderedEdge_iff_of_lt (g a) (g b) (g c)
        (g.strictMono hab) (g.strictMono hbc)).symm
    _ ↔ K.unorderedEdge (F (g a)) (F (g b)) (F (g c)) :=
      F.edge_iff (g a) (g b) (g c)
        (g.strictMono hab) (g.strictMono hbc)
    _ ↔ K.edge (F (g a)) (F (g b)) (F (g c)) :=
      K.unorderedEdge_iff_of_lt
        (F (g a)) (F (g b)) (F (g c))
        (hOrder hab) (hOrder hbc)

/-- Composing an ordered induced source copy ψ with the refined
generic embedding g and an initially unordered outer embedding F
produces a genuine ordered induced target copy. -/
def orderedComposite
    (F : UnorderedEmbedding G K)
    (g : Embedding G G)
    (hOrder : StrictMono (fun t => F (g t)))
    (ψ : Embedding H G) : Embedding H K where
  toFun := fun t => F (g (ψ t))
  strictMono := hOrder.comp ψ.strictMono
  edge_iff := by
    intro a b c hab hbc
    calc
      H.edge a b c ↔ G.edge (ψ a) (ψ b) (ψ c) :=
        ψ.edge_iff hab hbc
      _ ↔ K.edge (F (g (ψ a))) (F (g (ψ b)))
          (F (g (ψ c))) :=
        F.composed_ordered_edges g hOrder
          (ψ a) (ψ b) (ψ c)
          (ψ.strictMono hab) (ψ.strictMono hbc)

/-- The specifically constructed lower-bound fused self-embedding
automatically turns EVERY unordered external hypergraph embedding
into a strict enumerated induced embedding on its image. -/
noncomputable def orderedComposite_after_diaryFusion
    (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    {H : Ordered3Graph Nat}
    (ψ : Embedding H G.graph) :
    Embedding H K := by
  let g := ATRFiniteDecoder.orderedDiaryFusion G K F.toFun F.injective
  have hOrder : StrictMono (fun t => F (g t)) :=
    (ATRFiniteDecoder.orderedDiaryFusion_complete_native_stabilisation
      G K F.toFun F.injective).2.1
  exact F.orderedComposite g hOrder ψ

end UnorderedEmbedding
end Ordered3Graph
end ThreeUniformDiaries
