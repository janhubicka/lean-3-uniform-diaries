import ThreeUniformDiaries.DiaryFiniteAutTorsor
import ThreeUniformDiaries.FiniteAuxEmbeddingImage

/-!
# Track A: genuine finite ATR codes reflect unordered labelled copies

The finite ATR source is an ordered enumerated hypergraph, but the
finite A-copies whose colours are counted need not respect the
source's numerical order. The unordered ternary predicate has
six increasing-triple presentations.

We prove, with NO global tail assumption, that an actual finite
auxiliary embedding reflects the symmetric underlying hyperedge
predicate on arbitrary triples of actual finite source vertices.
The resulting pullback of a labelled A-copy uses the literal marked
source coordinates, not a different isomorphic copy.

This lemma is independent of the diary axioms, Ramsey theory,
unavoidability, and the sharp cardinal count.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

namespace FiniteAuxEmbedding

/-- Inducedness on actual finite increasing source triples is
equivalent to inducedness of the underlying UNORDERED hyperedge
relation for ANY triple of genuine finite source vertices.
In particular labels and the numerical order of their images
need not agree. -/
theorem unorderedEdge_iff_actual
    {H K : Ordered3Graph Nat} {f : Nat → Nat} {m : Nat}
    (E : FiniteAuxEmbedding H K f m)
    (a b c : Fin m) :
    H.unorderedEdge a.val b.val c.val ↔
      K.unorderedEdge (f a.val) (f b.val) (f c.val) := by
  have hOrder (i j : Fin m) :
      i.val < j.val ↔ f i.val < f j.val := by
    constructor
    · intro hij
      exact E.strictMono hij
    · intro h
      by_contra hn
      have hji : j.val ≤ i.val := Nat.le_of_not_gt hn
      exact (not_lt_of_ge (E.strictMono.monotone hji)) h
  have hTriple (i j k : Fin m) :
      (i.val < j.val ∧ j.val < k.val ∧
        H.edge i.val j.val k.val) ↔
      (f i.val < f j.val ∧ f j.val < f k.val ∧
        K.edge (f i.val) (f j.val) (f k.val)) := by
    constructor
    · rintro ⟨hij, hjk, he⟩
      exact ⟨(hOrder i j).mp hij,
        (hOrder j k).mp hjk,
        (E.edge_iff i.val j.val k.val hij hjk k.isLt).mp he⟩
    · rintro ⟨hij, hjk, he⟩
      have hij' := (hOrder i j).mpr hij
      have hjk' := (hOrder j k).mpr hjk
      exact ⟨hij', hjk',
        (E.edge_iff i.val j.val k.val hij' hjk' k.isLt).mpr he⟩
  unfold Ordered3Graph.unorderedEdge
  exact or_congr (hTriple a b c)
    (or_congr (hTriple a c b)
      (or_congr (hTriple b a c)
        (or_congr (hTriple b c a)
          (or_congr (hTriple c a b) (hTriple c b a)))))

/-- Pull back a labelled induced finite A-copy along an actual
finite auxiliary embedding, including all NON-INCREASING
labelled triples. Source labels may occur in any order. -/
theorem pullback_labelledCopy
    {H K : Ordered3Graph Nat} {f : Nat → Nat} {m : Nat}
    (E : FiniteAuxEmbedding H K f m)
    (A : Ordered3Graph Nat) (a : Nat)
    (mark : Fin a → Fin m)
    (hCopy : IsFiniteLabelledCopy A K a
      (fun i => f (mark i).val)) :
    IsFiniteLabelledCopy A H a
      (fun i => (mark i).val) := by
  refine ⟨?_, ?_⟩
  · intro i j heq
    apply hCopy.1
    exact congrArg f heq
  · intro i j k
    exact (hCopy.2 i j k).trans
      (E.unorderedEdge_iff_actual
        (mark i) (mark j) (mark k)).symm

end FiniteAuxEmbedding

namespace FiniteAuxEmbeddingImage

/-- An extensional actual finite ATR code can pull back a
labelled induced copy, without inspecting a chosen infinite
tail of the finite code. -/
theorem pullback_labelledCopy
    {H K : Ordered3Graph Nat} {m : Nat}
    (e : FiniteAuxEmbeddingImage H K m)
    (A : Ordered3Graph Nat) (a : Nat)
    (mark : Fin a → Fin m)
    (hCopy : IsFiniteLabelledCopy A K a
      (fun i => e.image (mark i))) :
    IsFiniteLabelledCopy A H a
      (fun i => (mark i).val) := by
  obtain ⟨f, hf, he⟩ := e.admissible
  have hFun :
      (fun i : Fin a => e.image (mark i)) =
      (fun i : Fin a => f (mark i).val) := by
    funext i
    exact he (mark i)
  rw [hFun] at hCopy
  exact hf.pullback_labelledCopy A a mark hCopy

end FiniteAuxEmbeddingImage
end Ordered3Graph
end ThreeUniformDiaries
