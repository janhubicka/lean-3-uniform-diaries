import ThreeUniformDiaries.DiaryFiniteInducedMeetsIntoCountable
import ThreeUniformDiaries.DiaryUnorderedEmbedding

/-!
# Finite lower bound with the printed universal-hypergraph hypothesis

The manuscript assumes a countable universal hypergraph U and a
possibly non-order-preserving induced embedding F:U -> leaves(K).
The existing finite strong-unavoidability theorem uses an unordered
copy of the enumerated generic G inside the leaves of K.

This module verifies the exact bridge, including unordered
composition: universality supplies an UNORDERED induced copy
i:G -> U, and F o i remains induced on unordered triples, with
image in the original prescribed F[U]. No increasing enumeration
of U is required. This discharges the finite-source quantifier
gap without claiming any countable-source unavoidability.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- The symmetric unordered triple predicate is invariant under
all permutations, including the two adjacent transpositions. -/
theorem unorderedEdge_swap_first
    (G : Ordered3Graph Nat) (a b c : Nat) :
    G.unorderedEdge a b c ↔ G.unorderedEdge b a c := by
  unfold unorderedEdge
  constructor <;> intro h <;> convert h using 1 <;> ac_rfl

theorem unorderedEdge_swap_last
    (G : Ordered3Graph Nat) (a b c : Nat) :
    G.unorderedEdge a b c ↔ G.unorderedEdge a c b := by
  unfold unorderedEdge
  constructor <;> intro h <;> convert h using 1 <;> ac_rfl

theorem unorderedEdge_rotate
    (G : Ordered3Graph Nat) (a b c : Nat) :
    G.unorderedEdge a b c ↔ G.unorderedEdge b c a := by
  unfold unorderedEdge
  constructor <;> intro h <;> convert h using 1 <;> ac_rfl

theorem unorderedEdge_rotate_back
    (G : Ordered3Graph Nat) (a b c : Nat) :
    G.unorderedEdge a b c ↔ G.unorderedEdge c a b := by
  unfold unorderedEdge
  constructor <;> intro h <;> convert h using 1 <;> ac_rfl

theorem unorderedEdge_reverse
    (G : Ordered3Graph Nat) (a b c : Nat) :
    G.unorderedEdge a b c ↔ G.unorderedEdge c b a := by
  unfold unorderedEdge
  constructor <;> intro h <;> convert h using 1 <;> ac_rfl

namespace UnorderedEmbedding

variable {H U K : Ordered3Graph Nat}

/-- Induced unordered embeddings preserve the symmetric edge
predicate on ANY triple of distinct vertices, not just increasing
triples of the enumerated source. This is the prerequisite for
composition of two unordered embeddings. -/
theorem edge_iff_distinct
    (F : UnorderedEmbedding H K)
    (a b c : Nat)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    H.unorderedEdge a b c ↔
      K.unorderedEdge (F a) (F b) (F c) := by
  by_cases hAB : a < b
  · by_cases hBC : b < c
    · exact F.edge_iff a b c hAB hBC
    · have hCB : c < b := by omega
      by_cases hAC : a < c
      · calc
          H.unorderedEdge a b c ↔ H.unorderedEdge a c b :=
            H.unorderedEdge_swap_last a b c
          _ ↔ K.unorderedEdge (F a) (F c) (F b) :=
            F.edge_iff a c b hAC hCB
          _ ↔ K.unorderedEdge (F a) (F b) (F c) :=
            (K.unorderedEdge_swap_last (F a) (F b) (F c)).symm
      · have hCA : c < a := by omega
        calc
          H.unorderedEdge a b c ↔ H.unorderedEdge c a b :=
            H.unorderedEdge_rotate_back a b c
          _ ↔ K.unorderedEdge (F c) (F a) (F b) :=
            F.edge_iff c a b hCA hAB
          _ ↔ K.unorderedEdge (F a) (F b) (F c) :=
            (K.unorderedEdge_rotate_back (F a) (F b) (F c)).symm
  · have hBA : b < a := by omega
    by_cases hAC : a < c
    · calc
        H.unorderedEdge a b c ↔ H.unorderedEdge b a c :=
          H.unorderedEdge_swap_first a b c
        _ ↔ K.unorderedEdge (F b) (F a) (F c) :=
          F.edge_iff b a c hBA hAC
        _ ↔ K.unorderedEdge (F a) (F b) (F c) :=
          (K.unorderedEdge_swap_first (F a) (F b) (F c)).symm
    · have hCA : c < a := by omega
      by_cases hBC : b < c
      · calc
          H.unorderedEdge a b c ↔ H.unorderedEdge b c a :=
            H.unorderedEdge_rotate a b c
          _ ↔ K.unorderedEdge (F b) (F c) (F a) :=
            F.edge_iff b c a hBC hCA
          _ ↔ K.unorderedEdge (F a) (F b) (F c) :=
            (K.unorderedEdge_rotate (F a) (F b) (F c)).symm
      · have hCB : c < b := by omega
        calc
          H.unorderedEdge a b c ↔ H.unorderedEdge c b a :=
            H.unorderedEdge_reverse a b c
          _ ↔ K.unorderedEdge (F c) (F b) (F a) :=
            F.edge_iff c b a hCB hBA
          _ ↔ K.unorderedEdge (F a) (F b) (F c) :=
            (K.unorderedEdge_reverse (F a) (F b) (F c)).symm

/-- Unordered induced 3-hypergraph embeddings really compose,
without any monotonicity assumption on either factor. -/
def comp (F : UnorderedEmbedding U K)
    (i : UnorderedEmbedding H U) :
    UnorderedEmbedding H K where
  toFun := fun a => F (i a)
  injective := by
    intro a b hab
    exact i.injective (F.injective hab)
  edge_iff := by
    intro a b c hab hbc
    have hiab : i a ≠ i b := by
      intro h
      exact (ne_of_lt hab) (i.injective h)
    have hiac : i a ≠ i c := by
      intro h
      exact (ne_of_lt (lt_trans hab hbc)) (i.injective h)
    have hibc : i b ≠ i c := by
      intro h
      exact (ne_of_lt hbc) (i.injective h)
    exact (i.edge_iff a b c hab hbc).trans
      (F.edge_iff_distinct (i a) (i b) (i c) hiab hiac hibc)

end UnorderedEmbedding

/-- Literal countable (unordered) universality used in the
manuscript, restricted to enumerations on Nat. In particular
a universal hypergraph contains the enumerated generic one
as an induced UNORDERED hypergraph. -/
def CountablyUniversal (U : Ordered3Graph Nat) : Prop :=
  ∀ H : Ordered3Graph Nat, Nonempty (UnorderedEmbedding H U)

end Ordered3Graph

namespace DiaryLeafPriority

/-- Finite-source diary unavoidability under the precise manuscript
hypotheses: K is any countable full diary, U is an arbitrary
countable universal unordered 3-hypergraph, and F:U -> leaves(K)
is a prescribed unordered induced embedding. The output keeps
every source leaf in F[U] and is induced with ALL meet levels. -/
theorem exists_finiteDiary_full_embedding_in_universal_leaf_range
    {A U K : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (G : GenericEnumerated3Graph)
    (hUniversal : Ordered3Graph.CountablyUniversal U)
    (F : Ordered3Graph.UnorderedEmbedding U K)
    (hFleaf : ∀ u, IsLeaf K (F u))
    (DK : RoleDiary K) :
    ∃ f : Nat → Nat,
      FiniteMeetEmbedding A K n f ∧
      (∀ u : Nat, 3 ≤ u → u < n → IsLeaf A u →
        ∃ t : Nat, f u = F t) := by
  classical
  let i : Ordered3Graph.UnorderedEmbedding G.graph U :=
    Classical.choice (hUniversal G.graph)
  let Fi : Ordered3Graph.UnorderedEmbedding G.graph K := F.comp i
  have hFiLeaf : ∀ u, IsLeaf K (Fi u) := by
    intro u
    exact hFleaf (i u)
  obtain ⟨f,hFull,hRange⟩ :=
    exists_finiteDiary_full_embedding_in_generic_leaf_range
      DA G Fi hFiLeaf DK
  refine ⟨f,hFull,?_⟩
  intro u hu3 hun huLeaf
  obtain ⟨t,ht⟩ := hRange u hu3 hun huLeaf
  exact ⟨i t,ht⟩

end DiaryLeafPriority
end ThreeUniformDiaries
