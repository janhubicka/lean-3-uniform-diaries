import ThreeUniformDiaries.DiaryLowerCanonicalMarkedColour
import ThreeUniformDiaries.DiaryLowerCanonicalColourUnavoidability

/-!
# Track C: unmarked diary source is independent of the labels of a copy

The lower bound for ACTUAL labelled A-embeddings was certified in #1113.
For UNLABELLED A-copies the colour should be the underlying finite
full diary source of that canonical marked colour. Unlike the full
marked source, this underlying diary must not change under a
different A-marking of the SAME finite vertex set.

This module establishes that property by literal support equality,
not by identifying isomorphic sources or dividing an arbitrary
colour count by |Aut(A)|. In particular all A-label permutations
and the empty finite source are allowed.

A subsequent Track C module can use this theorem to define a
total unmarked colour and prove its unavoidability in every
unordered induced self-copy, matching the already verified sharp
UNLABELLED upper bound.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open _root_.ThreeUniformDiaries.Ordered3Graph
open DiaryLeafPriority

/-- A finite source is determined by its numerical size and
its entire zero-extended induced ternary edge table, INCLUDING
nonedges. Proof fields are irrelevant. -/
theorem protectedSource_eq_of_size_and_graph
    (S T : ProtectedSource 0)
    (hSize : S.k = T.k)
    (hGraph : S.picture.toOrdered3Graph = T.picture.toOrdered3Graph) :
    S = T := by
  cases S with
  | mk m P hP =>
    cases T with
    | mk n Q hQ =>
      change m = n at hSize
      subst n
      have hPQ : P = Q := by
        calc
          P = P.toOrdered3Graph.initialSegment (m + 1) :=
            (EnumNode.initialSegment_toOrdered3Graph_self P).symm
          _ = Q.toOrdered3Graph.initialSegment (m + 1) := by
            rw [hGraph]
          _ = Q :=
            EnumNode.initialSegment_toOrdered3Graph_self Q
      cases hPQ
      rfl

/-- For two genuine labelled A-copies on the SAME finite set of
diary leaves, their canonical marked colours have LITERALLY
the same unmarked finite full diary source. Different choices of
the labelled marking are permitted, including non-order-preserving
ones. -/
theorem canonicalMarkedSourceOfLeaves_source_eq_of_same_range
    {K : Ordered3Graph Nat} (D : RoleDiary K)
    {a : Nat} (A : EnumNode a)
    (v w : Fin a → Nat)
    (hvLeaf : ∀ i : Fin a, IsLeaf K (v i))
    (hwLeaf : ∀ i : Fin a, IsLeaf K (w i))
    (hvCopy : IsInducedLabelledCopy A K v)
    (hwCopy : IsInducedLabelledCopy A K w)
    (hRange : (Finset.univ : Finset (Fin a)).image v =
      (Finset.univ : Finset (Fin a)).image w) :
    (canonicalMarkedSourceOfLeaves D A v hvLeaf hvCopy).source =
      (canonicalMarkedSourceOfLeaves D A w hwLeaf hwCopy).source := by
  classical
  obtain ⟨_hvMem, hvSize, hvGraph, _hvIndex⟩ :=
    canonicalMarkedSourceOfLeaves_spec D A v hvLeaf hvCopy
  obtain ⟨_hwMem, hwSize, hwGraph, _hwIndex⟩ :=
    canonicalMarkedSourceOfLeaves_spec D A w hwLeaf hwCopy
  rw [← hRange] at hwSize hwGraph
  have hSize :
      (canonicalMarkedSourceOfLeaves D A v hvLeaf hvCopy).source.k =
      (canonicalMarkedSourceOfLeaves D A w hwLeaf hwCopy).source.k := by
    omega
  have hGraph :
      (canonicalMarkedSourceOfLeaves D A v hvLeaf hvCopy).source.picture.toOrdered3Graph =
      (canonicalMarkedSourceOfLeaves D A w hwLeaf hwCopy).source.picture.toOrdered3Graph :=
    hvGraph.trans hwGraph.symm
  exact protectedSource_eq_of_size_and_graph
    _ _ hSize hGraph

/-- After a fixed unordered leaf identification F : U -> K,
relabeling an actual induced A-copy without changing its
underlying vertex SET changes only its marked positions, and
not the canonically extracted unmarked diary shape. -/
theorem canonicalMarkedDiaryColour_source_eq_of_same_range
    {U K : Ordered3Graph Nat}
    (D : RoleDiary K)
    (F : UnorderedEmbedding U K)
    (hFLeaf : ∀ u : Nat, IsLeaf K (F u))
    {a : Nat} (A : EnumNode a)
    (v w : GenuineFiniteEmbeddings A U)
    (hRange : (Finset.univ : Finset (Fin a)).image v.val =
      (Finset.univ : Finset (Fin a)).image w.val) :
    (canonicalMarkedDiaryColour D F hFLeaf A v).val.source =
      (canonicalMarkedDiaryColour D F hFLeaf A w).val.source := by
  classical
  let fv : Fin a → Nat := fun i => F (v.val i)
  let fw : Fin a → Nat := fun i => F (w.val i)
  have hLeafv : ∀ i : Fin a, IsLeaf K (fv i) :=
    fun i => hFLeaf (v.val i)
  have hLeafw : ∀ i : Fin a, IsLeaf K (fw i) :=
    fun i => hFLeaf (w.val i)
  have hCopyv : IsInducedLabelledCopy A K fv :=
    isInducedLabelledCopy_map_unordered A F v.val v.property
  have hCopyw : IsInducedLabelledCopy A K fw :=
    isInducedLabelledCopy_map_unordered A F w.val w.property
  have hRangeF :
      (Finset.univ : Finset (Fin a)).image fv =
        (Finset.univ : Finset (Fin a)).image fw := by
    calc
      (Finset.univ : Finset (Fin a)).image fv =
          ((Finset.univ : Finset (Fin a)).image v.val).image F := by
        simp only [Finset.image_image, Function.comp_def, fv]
      _ = ((Finset.univ : Finset (Fin a)).image w.val).image F :=
        congrArg (fun L : Finset Nat => L.image F) hRange
      _ = (Finset.univ : Finset (Fin a)).image fw := by
        simp only [Finset.image_image, Function.comp_def, fw]
  have hSource :=
    canonicalMarkedSourceOfLeaves_source_eq_of_same_range
      D A fv fw hLeafv hLeafw hCopyv hCopyw hRangeF
  change (canonicalMarkedSourceOfLeaves D A fv hLeafv hCopyv).source =
    (canonicalMarkedSourceOfLeaves D A fw hLeafw hCopyw).source
  exact hSource

end ATRFiniteDecoder
end ThreeUniformDiaries
