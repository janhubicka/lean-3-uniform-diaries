import ThreeUniformDiaries.DiaryFiniteLeafMeetPrefixCompression
import ThreeUniformDiaries.DiaryFiniteEOneSplitLex

/-!
# Retained one-split disagreement gives exact compressed leaf meets

Deleting test levels from a diary cannot introduce earlier type
disagreement. A selected leaf pair a<b with original singleton
meet m therefore agrees through the new index k for m.

If m is a genuine old one-split and all three markers, m, a, b
are retained, E1--E5 identify its first disagreement with the
zero-marker bits (0,m,a) and (0,m,b). These are literally retained
under increasing induced reindexing. Hence the compressed meet
is EXACTLY k, not a later cut.

The lemma is stated for a general finite support carrying those
three vertices at genuine increasing indices, so it can be reused
for the concrete support generated from a finite set of leaves.
It is the verified target form of the proposed extraction
equation for selected singleton leaf meets. S2/full pair-meet
first disagreements require separate analogous treatment.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {G : Ordered3Graph Nat} {S : Finset Nat}

/-- If an increasing finite induced restriction contains a source
one-split m and two source leaves whose first singleton meet is m,
the copied split's own zero-marker disagreement ensures EXACT
numerical first-meet preservation, even though other old test
vertices may have been deleted. -/
theorem finiteSupportGraph_oneMeet_exact_at_retained_oneSplit
    (D : RoleDiary G)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S)
    (i j k a b m : Nat)
    (hi : i < S.card) (hj : j < S.card) (hk : k < S.card)
    (hij : i < j) (hk3 : 3 ≤ k)
    (hki : k < i) (hkj : k < j)
    (hIa : finiteSupportIndex S i = a)
    (hJb : finiteSupportIndex S j = b)
    (hKm : finiteSupportIndex S k = m)
    (hSplit : IsOneSplit G m)
    (hMeet : G.oneMeetLevel a b = m) :
    (finiteSupportGraph G S).oneMeetLevel i j = k := by
  classical
  let T := finiteSupportGraph G S
  have hab : a < b := by
    have hStrict := finiteSupportIndex_strictMono S i j hij hj
    omega
  have hma : m < a := by
    have hStrict := finiteSupportIndex_strictMono S k i hki hi
    omega
  have hSourceAt : G.SameOneTypeBelow m a b := by
    rw [← hMeet]
    exact G.oneMeetLevel_agree a b
  have hAtTarget : T.SameOneTypeBelow k i j := by
    apply finiteSupportGraph_oneType_of_original
      (G := G) (S := S) k i j hk hi hj
        (by omega) (by omega)
    simpa only [hKm,hIa,hJb] using hSourceAt
  have hCap : k ≤ min i j := by omega
  have hLower : k ≤ T.oneMeetLevel i j :=
    Nat.le_findGreatest hCap hAtTarget
  have hOldDifferent :
      ¬ (G.edge 0 m a ↔ G.edge 0 m b) :=
    E_oneSplit_distinguishing_zero_bit
      D.permitted_edge m a b hSplit hab hma hMeet
  have ⟨_,hZero,_,_⟩ :=
    finiteSupportIndex_initial_markers S h0 h1 h2
  have hEdgeA :
      T.edge 0 k i ↔ G.edge 0 m a := by
    have hEdge := finiteSupportGraph_edge_iff
      G S 0 k i (by omega) (by omega) hi
    simpa only [hZero,hKm,hIa] using hEdge
  have hEdgeB :
      T.edge 0 k j ↔ G.edge 0 m b := by
    have hEdge := finiteSupportGraph_edge_iff
      G S 0 k j (by omega) (by omega) hj
    simpa only [hZero,hKm,hJb] using hEdge
  have hTargetDifferent :
      ¬ (T.edge 0 k i ↔ T.edge 0 k j) := by
    intro h
    exact hOldDifferent (hEdgeA.symm.trans (h.trans hEdgeB))
  have hNextFail : ¬ T.SameOneTypeBelow (k + 1) i j := by
    intro h
    exact hTargetDifferent (h (a := 0) (b := k) (by omega) (by omega))
  have hUpper : T.oneMeetLevel i j < k + 1 := by
    by_contra hbad
    have hGe : k + 1 ≤ T.oneMeetLevel i j := by omega
    have hAgree := T.oneMeetLevel_agree i j
    apply hNextFail
    intro a' b' hab' hb'
    exact hAgree hab' (by omega)
  change T.oneMeetLevel i j = k
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
