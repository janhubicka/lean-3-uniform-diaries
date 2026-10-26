import ThreeUniformDiaries.DiaryFiniteCanonicalCausalRoleCensus
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalOriginalV3
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalMarkerGraph

/-!
# COMPLETE literal V3 on all actual finite sign-rooted target leaves

The exact role census shows that every leaf of the finished finite
canonical causal graph is an indexed source leaf on some original
canonical flip branch. Every pair of these indexed source leaves
has exactly two possibilities:

* Both occur together, in increasing order, on SOME original flip
  branch. Both literal V3 marker equivalences on such a pair have
  already been proved by exact marker ranks, exact singleton/pointed
  auxiliary meets, and literal LexEarlier transport (#908).
* They do not occur together on any original flip branch. Their
  numerical indices are increasing, hence the actual off-branch
  mask selects them, and the causal marker completion proves BOTH
  literal V3 clauses on that pair (#903).

This exhausts all ordered pairs of actual leaves in the finite
completed graph and proves the whole V3 part of a bounded
FiniteRolePrediaryBlock, not just its branch-by-branch cases.

The full V1/V2 positive-class coherence, bounded split witnesses,
E1--E5 permitted edges, and strong finite flip absorption are
still separate mathematical obligations.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Both literal Devlin marker laws for an arbitrary ordered
pair of TRUE leaves in the finite canonical causal graph.
The pair need not occur in a single source-flip branch. -/
theorem finiteCanonicalCausalMarkerGraph_all_leaf_pairs_V3
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (a b : Nat) (hab : a < b)
    (hb : b < Fintype.card (FiniteCanonicalSignRootedVertex DA))
    (haLeaf : IsLeaf (finiteCanonicalCausalMarkerGraph DA) a)
    (hbLeaf : IsLeaf (finiteCanonicalCausalMarkerGraph DA) b) :
    ((finiteCanonicalCausalMarkerGraph DA).edge 1 a b ↔
      LexEarlier (finiteCanonicalCausalMarkerGraph DA) a b) ∧
    ((finiteCanonicalCausalMarkerGraph DA).edge 2 a b ↔
      ¬ LexEarlier (finiteCanonicalCausalMarkerGraph DA) a b) := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  have haBound : a < Fintype.card (FiniteCanonicalSignRootedVertex DA) :=
    by omega
  obtain ⟨i,u,hun,hu,hIdxA⟩ :=
    finiteCanonicalCausalMarkerGraph_leaf_census
      DA a haBound haLeaf
  obtain ⟨j,v,hvn,hv,hIdxB⟩ :=
    finiteCanonicalCausalMarkerGraph_leaf_census
      DA b hb hbLeaf
  let X : FiniteCanonicalSignRootedVertex DA :=
    finiteCanonicalNodeAt DA i u hun
  let Y : FiniteCanonicalSignRootedVertex DA :=
    finiteCanonicalNodeAt DA j v hvn
  have hRankXY :
      (finiteCanonicalNodeIndex DA X).val <
      (finiteCanonicalNodeIndex DA Y).val := by
    change (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u hun)).val <
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA j v hvn)).val
    rw [hIdxA,hIdxB]
    exact hab
  have hBefore :
      finiteCanonicalNodeBeforeAmbient DA X.val Y.val :=
    (finiteCanonicalNodeBefore_iff_ambient DA X Y).mp
      ((finiteCanonicalNodeBefore_iff_rank_lt DA X Y).mpr hRankXY)
  by_cases hShared : F.SharedBranchPair X.val Y.val
  · obtain ⟨k,x,y,hxy,hyn,hNodeX,hNodeY⟩ := hShared
    have hxU : x = u := by
      have h := congrArg Prod.fst hNodeX
      have hLevel : X.val.1 = u :=
        finiteCanonicalNodeAt_level DA i u hun
      simpa only [FiniteSignRootedFlipFamily.node_level,hLevel] using h
    have hyV : y = v := by
      have h := congrArg Prod.fst hNodeY
      have hLevel : Y.val.1 = v :=
        finiteCanonicalNodeAt_level DA j v hvn
      simpa only [FiniteSignRootedFlipFamily.node_level,hLevel] using h
    subst x
    subst y
    have hSubX : finiteCanonicalNodeAt DA k u hun = X := by
      apply Subtype.ext
      exact hNodeX
    have hSubY : finiteCanonicalNodeAt DA k v hvn = Y := by
      apply Subtype.ext
      exact hNodeY
    have hXRank :
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA k u hun)).val = a := by
      rw [hSubX]
      exact hIdxA
    have hYRank :
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA k v hvn)).val = b := by
      rw [hSubY]
      exact hIdxB
    have hBranch := finiteCanonicalCausalMarkerGraph_original_branch_V3
      DA k u v hxy hvn hu hv
    simpa only [hXRank,hYRank] using hBranch
  · have hLeafX : IsLeaf A X.val.1 := by
      simpa only [X,finiteCanonicalNodeAt,
        FiniteSignRootedFlipFamily.node_level] using hu
    have hLeafY : IsLeaf A Y.val.1 := by
      simpa only [Y,finiteCanonicalNodeAt,
        FiniteSignRootedFlipFamily.node_level] using hv
    have hOff :
        F.OrderedOffBranchLeafPair
          (finiteCanonicalNodeBeforeAmbient DA) X.val Y.val :=
      ⟨hLeafX,hLeafY,hBefore,hShared⟩
    have hMask : finiteCanonicalRankedOffBranchMask DA a b := by
      refine ⟨X,Y,?_,?_,hOff⟩
      · exact hIdxA
      · exact hIdxB
    exact ⟨
      finiteCanonicalCausalMarkerGraph_offbranch_marker_one DA a b hMask,
      finiteCanonicalCausalMarkerGraph_offbranch_marker_two DA a b hMask⟩

/-- Exactly the TWO complete bounded Devlin V3 fields from the
manuscript's FiniteRolePrediaryBlock definition, now checked for
ALL actual leaves of the completed canonical causal graph. -/
theorem finiteCanonicalCausalMarkerGraph_complete_finite_V3
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    (∀ a b : Nat, a < b →
      b < Fintype.card (FiniteCanonicalSignRootedVertex DA) →
      IsLeaf (finiteCanonicalCausalMarkerGraph DA) a →
      IsLeaf (finiteCanonicalCausalMarkerGraph DA) b →
      ((finiteCanonicalCausalMarkerGraph DA).edge 1 a b ↔
        LexEarlier (finiteCanonicalCausalMarkerGraph DA) a b)) ∧
    (∀ a b : Nat, a < b →
      b < Fintype.card (FiniteCanonicalSignRootedVertex DA) →
      IsLeaf (finiteCanonicalCausalMarkerGraph DA) a →
      IsLeaf (finiteCanonicalCausalMarkerGraph DA) b →
      ((finiteCanonicalCausalMarkerGraph DA).edge 2 a b ↔
        ¬ LexEarlier (finiteCanonicalCausalMarkerGraph DA) a b)) := by
  constructor
  · intro a b hab hb ha hbLeaf
    exact (finiteCanonicalCausalMarkerGraph_all_leaf_pairs_V3
      DA a b hab hb ha hbLeaf).1
  · intro a b hab hb ha hbLeaf
    exact (finiteCanonicalCausalMarkerGraph_all_leaf_pairs_V3
      DA a b hab hb ha hbLeaf).2

end DiaryLeafPriority
end ThreeUniformDiaries
