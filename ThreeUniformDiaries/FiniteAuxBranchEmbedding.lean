import ThreeUniformDiaries.UniversalAuxBranchEmbedding
import ThreeUniformDiaries.TypeRepresentation

/-!
# Finite hypergraphs as branches of the uniform K_I construction

A finite enumerated H is regarded as the ordered 3-graph on Nat
obtained by declaring every out-of-range hyperedge absent. The initial
n vertices are unchanged and no type meet of vertices below |H|
can see the added isolated vertices above |H|.

The universal K_I branch embedding therefore applies without
a separate choice for each finite H.
-/

namespace ThreeUniformDiaries
namespace EnumNode

/-- The initial n vertices of the infinite zero extension of a
finite enumerated hypergraph are exactly its finite truncation. -/
theorem toOrdered3Graph_initialSegment
    {m : Nat} (A : EnumNode m) (n : Nat) :
    A.toOrdered3Graph.initialSegment n = A.truncate n := by
  apply EnumNode.ext_triples
  funext i j k
  by_cases h : i < j ∧ j < k ∧ k < n
  · have hiff :
        (A.toOrdered3Graph.initialSegment n).triple i j k = true ↔
          (A.truncate n).triple i j k = true := by
      calc
        (A.toOrdered3Graph.initialSegment n).triple i j k = true ↔
            A.toOrdered3Graph.edge i j k :=
          A.toOrdered3Graph.initialSegment_edge_iff h.1 h.2.1 h.2.2
        _ ↔ A.triple i j k = true := Iff.rfl
        _ ↔ (A.truncate n).triple i j k = true := by
          simp [EnumNode.truncate, h.2.2]
    cases ha : (A.toOrdered3Graph.initialSegment n).triple i j k <;>
      cases hb : (A.truncate n).triple i j k <;> simp_all
  · rw [(A.toOrdered3Graph.initialSegment n).support i j k h,
        (A.truncate n).support i j k h]

/-- A finite enumerated hypergraph with the prescribed initial
segment admits a fixed-prefix aux-type-respecting embedding in G. -/
theorem exists_finite_auxTypeEmbedding
    (G : GenericEnumerated3Graph)
    {m : Nat} (A : EnumNode m)
    (n : Nat)
    (hpre : G.graph.initialSegment n = A.truncate n) :
    ∃ e : Ordered3Graph.Embedding A.toOrdered3Graph G.graph,
      e.AuxTypeRespecting ∧
      (∀ k : Nat, k < n → e k = k) ∧
      (∀ u v : Nat,
        G.graph.oneMeetLevel (e u) (e v) =
          e (A.toOrdered3Graph.oneMeetLevel u v)) ∧
      (∀ u₀ u₁ v₀ v₁ : Nat, u₀ < u₁ → v₀ < v₁ →
        G.graph.auxMeetLevel (e u₀) (e u₁) (e v₀) (e v₁) =
          e (A.toOrdered3Graph.auxMeetLevel u₀ u₁ v₀ v₁)) := by
  let I := A.truncate n
  obtain ⟨E, phi, hphi⟩ :=
    exists_universal_auxEmbedding G I hpre
  have hA : A.toOrdered3Graph.initialSegment n = I :=
    A.toOrdered3Graph_initialSegment n
  obtain ⟨e, _, hfix, haux⟩ := hphi.2.2.2 A.toOrdered3Graph hA
  refine ⟨e, haux, hfix, ?_, ?_⟩
  · intro u v
    exact e.oneMeetLevel_eq_of_auxTypeRespecting haux u v
  · intro u₀ u₁ v₀ v₁ hu hv
    exact e.auxMeetLevel_eq_of_auxTypeRespecting haux
      u₀ u₁ v₀ v₁ hu hv

end EnumNode
end ThreeUniformDiaries
