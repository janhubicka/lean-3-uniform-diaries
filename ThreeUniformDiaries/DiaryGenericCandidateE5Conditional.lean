import ThreeUniformDiaries.DiaryCandidateE5NewLeafOnly
import ThreeUniformDiaries.DiaryOldLeafPairGenericSuccessor

/-!
# Track A: genericity discharges the E5 clause, conditionally on functionality

Fix an arbitrary genuine old RESERVED source diary stage whose selected
leaf images lie in one originally designated unordered copy of the
enumerated generic 3-hypergraph inside the target true leaves.

The verified generic one-point extension theorem gives an arbitrarily
late proposed next target leaf v in that SAME prescribed leaf range,
simultaneously realizing ALL requested triples/nontriples with pairs of
old selected leaves. The exact finite candidate E5 criterion shows
that, IF the complete new-leaf S1/S2 generator table for this v is
functional, it automatically satisfies every E5 edge/nonedge test on
the entire successor support.

The implication is deliberately conditional on functionality.
Generic leaf-reduct extension does not control E2/E3 marker/split bits,
numeric split positions, future spacing, or persistent continuation.
No full candidate or unconditional diary unavoidability is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- In the original prescribed unordered generic leaf range there
is an actually late genuine target leaf v for which the entire
new-supported E5 induced edge/nonedge table follows from functionality
of the finite S1/S2 generator relation.

The antecedent cannot be dropped by leaf-only genericity. -/
theorem exists_outer_generic_leaf_with_E5_of_functional_candidate
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H)
    (G : GenericEnumerated3Graph)
    (F : _root_.ThreeUniformDiaries.Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (f : Nat → Nat)
    (P : ReservedDiaryStage H K F m f)
    (hm : IsLeaf H m) :
    ∃ t : Nat,
      oldStageTailCut H m f < F t ∧
      IsLeaf K (F t) ∧
      (FiniteGeneratorTableFunctional
        (candidateNewLeafGeneratorTable H K m f (F t)) →
       ∀ a b c : Nat,
         a ∈ countableDiaryFiniteSupport H (m + 1) →
         b ∈ countableDiaryFiniteSupport H (m + 1) →
         c ∈ countableDiaryFiniteSupport H (m + 1) →
         IsLeaf H a → IsLeaf H b → IsLeaf H c →
         a < b → b < c →
         (H.edge a b c ↔
           K.edge
             (candidateNewLeafTableMap H K m f (F t) a)
             (candidateNewLeafTableMap H K m f (F t) b)
             (candidateNewLeafTableMap H K m f (F t) c))) := by
  obtain ⟨t, hLate, hLeaf, hOldPairs⟩ :=
    exists_fresh_outer_generic_leaf_realizing_all_old_leaf_pair_bits
      G F hFLeaf m f P
  refine ⟨t, hLate, hLeaf, ?_⟩
  intro hFunctional
  exact (P.1.functional_candidate_E5_iff_old_leaf_pair_bits
    DH hm hFunctional).mp hOldPairs

end DiaryLeafPriority
end ThreeUniformDiaries
