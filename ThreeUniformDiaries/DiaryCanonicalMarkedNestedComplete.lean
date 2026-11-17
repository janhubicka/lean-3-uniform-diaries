import ThreeUniformDiaries.DiaryCanonicalMarkedNestedGraph

/-!
# FULL nested marked-diary support identity (finite source)

For L' ⊆ L genuine leaves of a full RoleDiary K, let
S=S_K(L), T=S_K(L'), H=the finite graph reindexed from S,
and r=the increasing rank map into S.
Let V=S_H(r[L']).

The theorem packages the exact three assertions needed for
the appendix's nested-support lemma:

1. V is literally T.image r (full markers + S1 + full S2);
2. the induced finite graph on V in H is literally the
   induced finite graph on T in K, edges AND nonedges;
3. the final rank of every selected leaf in either
   construction is literally the same.

The only full diary assumption is that selected leaves of L
are genuine, needed for exact S1/S2 generator transport.
The second finite reindexing uses only general finite-set
and ordered-graph lemmas; no countable diary-unavoidability,
abstract Safe predicate or Ramsey theorem is used.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The exact nested support/induced graph/mark-rank compatibility
needed to restrict a canonical marked finite diary, including
arbitrary choices of labelled selected leaves. -/
theorem finiteLeafMeetSupport_nested_complete
    {K : Ordered3Graph Nat}
    (D : RoleDiary K)
    (L L' : Finset Nat)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf K u)
    (hSub : L' ⊆ L) :
    let S := finiteLeafMeetSupport K L
    let T := finiteLeafMeetSupport K L'
    let H := finiteSupportGraph K S
    let r := finiteSupportRank S
    let V := finiteLeafMeetSupport H (L'.image r)
    V = T.image r ∧
      finiteSupportGraph H V = finiteSupportGraph K T ∧
      (∀ u : Nat, u ∈ L' →
        finiteSupportRank V (r u) = finiteSupportRank T u) := by
  classical
  let S : Finset Nat := finiteLeafMeetSupport K L
  let T : Finset Nat := finiteLeafMeetSupport K L'
  let H : Ordered3Graph Nat := finiteSupportGraph K S
  let r : Nat → Nat := finiteSupportRank S
  let V : Finset Nat := finiteLeafMeetSupport H (L'.image r)
  change V = T.image r ∧
    finiteSupportGraph H V = finiteSupportGraph K T ∧
    (∀ u : Nat, u ∈ L' →
      finiteSupportRank V (r u) = finiteSupportRank T u)
  have hTS : T ⊆ S := finiteLeafMeetSupport_mono K L' L hSub
  have hSets : T.image r = V :=
    finiteLeafMeetSupport_nested_rank_image D L L' hLeaves hSub
  refine ⟨hSets.symm, ?_, ?_⟩
  · rw [← hSets]
    exact finiteSupportGraph_nested_rank_eq K S T hTS
  · intro u hu
    rw [← hSets]
    exact finiteSupportRank_nested_rank_image S T hTS
      u (mem_finiteLeafMeetSupport_leaf K L' u hu)

end DiaryLeafPriority
end ThreeUniformDiaries
