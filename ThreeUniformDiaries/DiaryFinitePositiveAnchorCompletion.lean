import ThreeUniformDiaries.DiaryFiniteDevlinFromSplitAnchors
import ThreeUniformDiaries.DiaryFinitePositiveTwoSplitAnchor
import ThreeUniformDiaries.DiaryFinitePermittedShapeTransfer
import ThreeUniformDiaries.DiaryFinitePullbackProtectedEmbedding

/-!
# Positive anchors upgrade a bounded leaf preembedding to FULL inducedness

Let f be a finite marker-fixing leaf preembedding between complete
bounded V/E/S diaries. Thus f already preserves the induced leaf
hypergraph, all roles, and the EXACT numerical meets of all leaf
singletons and ordered leaf pairs, but need not initially preserve
the split-containing edge table.

If f correctly transports just ONE positive leaf at every source
one-split and ONE positive ordered leaf pair at every source
two-split, then:
* E1 marker role edges agree by role preservation;
* E2 follows from the one-positive-leaf/meet reconstruction;
* E3 follows from the one-positive-pair/full-meet reconstruction;
* E4 Devlin marker edges follow from E2, S1 and V3;
* E5 all-leaf triples already agree by preembedding.
The E1--E5 SHAPE reflection lemma handles all nonedges too.

Consequently f is induced on EVERY increasing finite source
triple. The already Lean-verified induced leaf-preembedding
completion then gives exact singleton and FULL ordered pair
meets, including ALL mixed tuples involving split vertices.
No independent Boolean split controls are asserted.

This is a *conditional embedding completion criterion*. It does
not construct a coherent target for arbitrary source diaries:
making all anchor bits positive simultaneously is the remaining
geometric source of difficulty.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Inside a true finite prediary, a marker-one edge exactly
indicates a genuine one-split at that vertex, and marker-two
likewise indicates a two-split. -/
private theorem finite_role_marker_edges_iff
    {H : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRolePrediaryBlock H n)
    (u : Nat) (hu3 : 3 ≤ u) (hun : u < n) :
    (H.edge 0 1 u ↔ IsOneSplit H u) ∧
    (H.edge 0 2 u ↔ IsTwoSplit H u) := by
  have hRoles := D.role_valid u hu3 hun
  constructor
  · constructor
    · intro he
      rcases hRoles with hLeaf | hOne | hTwo
      · exact False.elim (hLeaf.2.1 he)
      · exact hOne
      · exact False.elim (hTwo.2.1 he)
    · intro h
      exact h.2.1
  · constructor
    · intro he
      rcases hRoles with hLeaf | hOne | hTwo
      · exact False.elim (hLeaf.2.2 he)
      · exact False.elim (hOne.2.2 he)
      · exact hTwo
    · intro h
      exact h.2.2

/-- Marker-1 and marker-2 ROLE incidences themselves are
transported under a bounded leaf preembedding. -/
theorem FiniteLeafPreembedding.role_marker_edge_iff
    {A B : Ordered3Graph Nat} {n k : Nat} {f : Nat → Nat}
    (DA : FiniteRolePrediaryBlock A n)
    (DB : FiniteRolePrediaryBlock B k)
    (Q : FiniteLeafPreembedding A B n k f)
    (u : Nat) (hu3 : 3 ≤ u) (hun : u < n) :
    (A.edge 0 1 u ↔ B.edge 0 1 (f u)) ∧
    (A.edge 0 2 u ↔ B.edge 0 2 (f u)) := by
  have huB3 : 3 ≤ f u := (Q.image_ge_three_iff u).mpr hu3
  have hunB : f u < k := Q.image_bound u hun
  have hA := finite_role_marker_edges_iff DA u hu3 hun
  have hB := finite_role_marker_edges_iff DB (f u) huB3 hunB
  have hRoles := Q.role_iff u hu3 hun
  exact ⟨hA.1.trans (hRoles.2.1.symm.trans hB.1.symm),
    hA.2.trans (hRoles.2.2.symm.trans hB.2.symm)⟩

/-- Correctly transporting one positive anchor at EACH source
split suffices to make a finite leaf preembedding induced on
all source edges and nonedges. In particular there is no
separate Devlin-marker or lex-order choice left to make. -/
theorem finite_leafPreembedding_induced_of_positive_split_anchors
    {A B : Ordered3Graph Nat} {n k : Nat}
    {f : Nat → Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (DB : FiniteRoleDiaryBlock B k)
    (Q : FiniteLeafPreembedding A B n k f)
    (hOne : ∀ s : Nat, IsOneSplit A s →
      ∃ a : Nat, IsLeaf A a ∧ s < a ∧ a < n ∧
        A.edge 0 s a ∧ B.edge 0 (f s) (f a))
    (hTwo : ∀ s : Nat, IsTwoSplit A s →
      ∃ a b : Nat, a < b ∧ b < n ∧
        IsLeaf A a ∧ IsLeaf A b ∧ s < a ∧
        A.edge s a b ∧ B.edge (f s) (f a) (f b)) :
    ∀ a b c : Nat, a < b → b < c → c < n →
      (B.edge (f a) (f b) (f c) ↔ A.edge a b c) := by
  have hDevlin :=
    finite_leafPreembedding_Devlin_of_positive_oneSplit_anchors
      DA DB Q hOne
  have hAtShape :
      ∀ a b c : Nat, a < b → b < c → c < n →
        PermittedDiaryEdge A a b c →
        (A.edge a b c ↔ B.edge (f a) (f b) (f c)) := by
    intro a b c hab hbc hcn hShape
    rcases hShape with hE1 | hE2 | hE3 | hE4 | hE5
    · rcases hE1 with ⟨rfl,hb,hc3⟩
      have hRoleMarker :=
        Q.role_marker_edge_iff DA.prediary DB.prediary c hc3 hcn
      rcases hb with rfl | rfl
      · simpa only [Q.marker_zero,Q.marker_one] using hRoleMarker.1
      · simpa only [Q.marker_zero,Q.marker_two] using hRoleMarker.2
    · rcases hE2 with ⟨rfl,hOneB,hLeafC⟩
      obtain ⟨u,hu,hbu,hun,hPosA,hPosB⟩ := hOne b hOneB
      have hE2Edge :=
        finite_leafPreembedding_oneSplit_E2_of_positive_anchor
          DA.prediary DB.prediary Q b u hOneB hu hbu hun
          hPosA hPosB c hcn hLeafC hbc
      simpa only [Q.marker_zero] using hE2Edge
    · rcases hE3 with ⟨hTwoA,hLeafB,hLeafC⟩
      obtain ⟨u,v,huv,hvn,hu,hv,hsu,hPosA,hPosB⟩ :=
        hTwo a hTwoA
      exact finite_leafPreembedding_twoSplit_E3_of_positive_anchor
        DA.prediary DB.prediary Q a u v hTwoA huv hsu hvn
        hu hv hPosA hPosB b c hbc hcn hLeafB hLeafC hab
    · rcases hE4 with ⟨ha,hLeafB,hLeafC⟩
      have hMarker := hDevlin b c hbc hcn hLeafB hLeafC
      rcases ha with rfl | rfl
      · simpa only [Q.marker_one] using hMarker.1
      · simpa only [Q.marker_two] using hMarker.2
    · rcases hE5 with ⟨hLeafA,hLeafB,hLeafC⟩
      exact (Q.leaf_edge_iff a b c hab hbc hcn
        hLeafA hLeafB hLeafC).symm
  intro a b c hab hbc hcn
  have hShape :=
    Q.permittedEdge_iff a b c hab hbc hcn
  constructor
  · intro hB
    have hPermB :=
      DB.prediary.permitted_edge (f a) (f b) (f c) hB
    have hPermA := hShape.mpr hPermB
    exact (hAtShape a b c hab hbc hcn hPermA).mpr hB
  · intro hA
    have hPermA := DA.prediary.permitted_edge a b c hA
    exact (hAtShape a b c hab hbc hcn hPermA).mp hA

/-- Main anchored completion theorem: preservation of numerical
leaf meets and just one positive witness at each split upgrades
a bounded leaf preembedding to a fully induced and completely
ALL-MEET-preserving finite diary embedding, including mixed tuples. -/
theorem finite_leafPreembedding_to_boundedEmbedding_of_positive_anchors
    {A B : Ordered3Graph Nat} {n k : Nat}
    {f : Nat → Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (DB : FiniteRoleDiaryBlock B k)
    (Q : FiniteLeafPreembedding A B n k f)
    (hOne : ∀ s : Nat, IsOneSplit A s →
      ∃ a : Nat, IsLeaf A a ∧ s < a ∧ a < n ∧
        A.edge 0 s a ∧ B.edge 0 (f s) (f a))
    (hTwo : ∀ s : Nat, IsTwoSplit A s →
      ∃ a b : Nat, a < b ∧ b < n ∧
        IsLeaf A a ∧ IsLeaf A b ∧ s < a ∧
        A.edge s a b ∧ B.edge (f s) (f a) (f b)) :
    FiniteBoundedMeetEmbedding A B n k f := by
  have hInduced :=
    finite_leafPreembedding_induced_of_positive_split_anchors
      DA DB Q hOne hTwo
  exact ⟨Q.toMeetEmbedding_of_induced
    DA.prediary DB.prediary hInduced,Q.image_bound⟩

end DiaryLeafPriority
end ThreeUniformDiaries
