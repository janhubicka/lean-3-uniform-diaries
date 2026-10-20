import ThreeUniformDiaries.DiaryFiniteSupportProtectedTwoMeet
import ThreeUniformDiaries.DiaryFiniteLeafMeetCompleteReduct

/-!
# Complete factorisation of protected finite diary copies

A supplied finite meet-preserving embedding A -> G can be
compressed through ANY finite induced support S containing its
entire finite source image. The canonical rank lift is still a
genuine FiniteMeetEmbedding, preserving:
* strict increasing order and markers 0,1,2;
* every edge and nonedge of the source finite frame;
* all literal leaf, one-split and two-split roles;
* EVERY numerical singleton meet of source nonmarker vertices;
* EVERY numerical full ordered-pair meet of source nonmarkers,
  including arbitrary mixed split/leaf comparisons.

A genuine countable ambient RoleDiary yields a canonical FINITE
diary S_L for a finite set of its leaves. Any supplied input copy
whose leaves lie in L therefore factors through this finite diary
with all protected numerical meets intact.

This does not establish ANY every-flip absorption assertion.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A G : Ordered3Graph Nat} {n : Nat} {f : Nat → Nat}

/-- A finite meet embedding factors as a full finite meet embedding
through every finite support that retains its complete finite image.
No countable diary axiom is needed for this generic compression. -/
theorem FiniteMeetEmbedding.through_finiteSupport
    (DA : FiniteRoleDiaryBlock A n)
    (E : FiniteMeetEmbedding A G n f)
    (S : Finset Nat)
    (hRange : ∀ u : Nat, u < n → f u ∈ S) :
    FiniteMeetEmbedding A (finiteSupportGraph G S) n
      (finiteSupportLift S n f) := by
  have hn3 : 3 ≤ n := DA.prediary.frame.length_ge_three
  have h0 : 0 ∈ S := by
    have hh := hRange 0 (by omega)
    rw [E.marker_zero] at hh
    exact hh
  have h1 : 1 ∈ S := by
    have hh := hRange 1 (by omega)
    rw [E.marker_one] at hh
    exact hh
  have h2 : 2 ∈ S := by
    have hh := hRange 2 (by omega)
    rw [E.marker_two] at hh
    exact hh
  have hm := finiteSupportLift_markers S n f hn3 h0 h1 h2
    E.marker_zero E.marker_one E.marker_two
  refine {
    strictMono := finiteSupportLift_strictMono S n f E.strictMono hRange
    marker_zero := hm.1
    marker_one := hm.2.1
    marker_two := hm.2.2
    edge_iff := ?_
    leaf_iff := ?_
    oneSplit_iff := ?_
    twoSplit_iff := ?_
    oneMeet := ?_
    twoMeet := ?_
  }
  · intro a b c hab hbc hc
    exact finiteSupportLift_edge_iff E hRange a b c hab hbc hc
  · intro u hu3 hu
    exact finiteSupportLift_leaf_iff E hRange h0 h1 h2 u hu3 hu
  · intro u hu3 hu
    exact finiteSupportLift_oneSplit_iff E hRange h0 h1 h2 u hu3 hu
  · intro u hu3 hu
    exact finiteSupportLift_twoSplit_iff E hRange h0 h1 h2 u hu3 hu
  · intro u v hu3 hu hv3 hv
    exact finiteSupportLift_oneMeet_exact E hRange u v hu3 hu hv3 hv
  · intro a b c d hab hcd ha3 ha hb3 hb hc3 hc hd3 hd
    exact finiteSupportLift_twoMeet_exact
      E hRange a b c d hab hcd ha3 ha hb3 hb hc3 hc hd3 hd

/-- The actual finite diary reduction contains the given
protected copy as a fully induced, role- and mixed-meet preserving
finite embedding, provided L includes all of its source leaf
images. The output is a complete bounded finite diary. -/
theorem FiniteMeetEmbedding.factor_through_leafMeetSupport
    (DA : FiniteRoleDiaryBlock A n)
    (DG : RoleDiary G)
    (E : FiniteMeetEmbedding A G n f)
    (L : Finset Nat)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    (hImageLeaves : ∀ u : Nat, 3 ≤ u → u < n →
      IsLeaf A u → f u ∈ L) :
    FiniteRoleDiaryBlock
      (finiteSupportGraph G (finiteLeafMeetSupport G L))
      (finiteLeafMeetSupport G L).card ∧
    FiniteMeetEmbedding A
      (finiteSupportGraph G (finiteLeafMeetSupport G L)) n
      (finiteSupportLift (finiteLeafMeetSupport G L) n f) := by
  constructor
  · exact finiteLeafMeetSupport_is_finiteDiary DG hLeaves
  · apply E.through_finiteSupport DA
      (finiteLeafMeetSupport G L)
    exact FiniteMeetEmbedding.range_subset_leafMeetSupport
      DA E L hImageLeaves

end DiaryLeafPriority
end ThreeUniformDiaries
