import ThreeUniformDiaries.ActualFiniteAuxRamseyUnconditional
import ThreeUniformDiaries.InfinitePrefixes

/-!
# Complete finite ATR theorem, including incompatible fixed prefixes

The protected-prefix case is the genuine heterogeneous Milliken
application. If the finite source and generic target disagree below n,
no induced finite embedding fixes n: the edge tests on the first n
vertices already contradict inducedness. In that case the Ramsey
conclusion is vacuous and the identity self-embedding is a witness.

The resulting theorem has no externally supplied K_I presentation,
auxiliary embedding, Halpern--Lauchli axiom, or initial-segment
compatibility hypothesis. It colours only the actual finite vertices.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

/-- A finite induced aux embedding fixing all source vertices below n
forces agreement of the source and target n-vertex prefixes. -/
theorem fixedFiniteAuxEmbedding_forces_initialSegment
    (G : GenericEnumerated3Graph)
    {n k : Nat} (hnk : n ≤ k + 1)
    (A : EnumNode (k + 1))
    (e : Ordered3Graph.FiniteAuxEmbeddingImage
      A.toOrdered3Graph G.graph (k + 1))
    (hfix : ∀ i : Fin (k + 1), i.val < n → e.image i = i.val) :
    A.truncate n = G.graph.initialSegment n := by
  classical
  obtain ⟨f, hf, hval⟩ := e.admissible
  have hfixF : ∀ i : Nat, i < n → f i = i := by
    intro i hi
    have him : i < k + 1 := lt_of_lt_of_le hi hnk
    calc
      f i = e.image ⟨i, him⟩ := (hval ⟨i, him⟩).symm
      _ = i := hfix ⟨i, him⟩ hi
  apply EnumNode.ext_triples
  funext i j l
  by_cases hvalid : i < j ∧ j < l ∧ l < n
  · obtain ⟨hij, hjl, hln⟩ := hvalid
    have hlm : l < k + 1 := lt_of_lt_of_le hln hnk
    have hiff : A.triple i j l = true ↔ G.graph.edge i j l := by
      have h := hf.edge_iff i j l hij hjl hlm
      change (A.triple i j l = true ↔
        G.graph.edge (f i) (f j) (f l)) at h
      simpa only [hfixF i (by omega), hfixF j (by omega),
        hfixF l hln] using h
    change (if l < n then A.triple i j l else false) =
      decide (i < j ∧ j < l ∧ l < n ∧ G.graph.edge i j l)
    rw [ite_eq_left hln]
    cases hbit : A.triple i j l with
    | false =>
        have hnedge : ¬ G.graph.edge i j l := by
          intro hedge
          have hh : A.triple i j l = true := hiff.mpr hedge
          rw [hbit] at hh
          cases hh
        simp [hbit, hij, hjl, hln, hnedge]
    | true =>
        have hedge : G.graph.edge i j l := hiff.mp hbit
        simp [hbit, hij, hjl, hln, hedge]
  · have hs := (A.truncate n).support i j l hvalid
    have ht := (G.graph.initialSegment n).support i j l hvalid
    exact hs.trans ht.symm

/-- The manuscript's full finite auxiliary type-respecting Ramsey
theorem. No initial-segment compatibility or K_I presentation is
assumed. The witness fixes n, and postcomposition colours are
constant on all genuine finite aux embeddings also fixing n. -/
theorem actualFiniteAuxRamsey_allFinite
    (G : GenericEnumerated3Graph)
    {n k : Nat} (hnk : n ≤ k + 1)
    (A : EnumNode (k + 1))
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : Ordered3Graph.FiniteAuxEmbeddingImage
      A.toOrdered3Graph G.graph (k + 1) → κ) :
    ∃ (u : Ordered3Graph.Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
        (∀ j < n, u j = j) ∧
        ∃ color : κ,
          ∀ e : Ordered3Graph.FiniteAuxEmbeddingImage
              A.toOrdered3Graph G.graph (k + 1),
            (∀ i : Fin (k + 1), i.val < n → e.image i = i.val) →
            χ (e.postcompose u hu) = color := by
  let I : EnumNode n := G.graph.initialSegment n
  by_cases hAI : A.truncate n = I
  · exact actualFiniteAuxRamsey_matchingPrefix
      G hnk A I rfl hAI χ
  · let u : Ordered3Graph.Embedding G.graph G.graph := {
      toFun := fun i => i
      strictMono := by intro i j hij; exact hij
      edge_iff := by intro i j l hij hjl; exact Iff.rfl
    }
    have hu : u.AuxTypeRespecting := by
      constructor
      · intro l a b hla hlb
        exact Iff.rfl
      · intro l a b c d hla hab hlc hcd
        exact Iff.rfl
    refine ⟨u, hu, ?_, ?_⟩
    · intro j hj
      rfl
    · refine ⟨Classical.choice inferInstance, ?_⟩
      intro e hfix
      have hprefix := fixedFiniteAuxEmbedding_forces_initialSegment
        G hnk A e hfix
      exact False.elim (hAI hprefix)

end ATRFiniteDecoder
end ThreeUniformDiaries
