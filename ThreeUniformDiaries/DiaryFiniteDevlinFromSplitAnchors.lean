import ThreeUniformDiaries.DiaryFinitePositiveOneSplitAnchor
import ThreeUniformDiaries.DiaryFiniteEOneSplitLex
import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface
import ThreeUniformDiaries.DiaryFiniteLeafPreembeddingComposition

/-!
# Devlin marker edges follow automatically from one-split anchors

A finite diary preembedding preserves roles and genuine numerical
singleton meets of all leaf pairs. If a single positive leaf anchor
at each source one-split is taken to a positive target anchor, the
positive-one-split E2 transfer lemma preserves its entire column.

The E-only lexicographic formula at a leaf pair (u,v) says that
LexEarlier(u,v) is exactly the right-leaf E2 incidence at the
pair's genuine singleton meet. Therefore all LexEarlier relations
between leaves are preserved, although a bare leaf preembedding
does not generally preserve these orders.

V3 then forces BOTH actual Devlin marker edges (1,u,v) and
(2,u,v) to be induced automatically. This is the E4
piece needed to upgrade anchored finite leaf preembeddings to
full induced diary embeddings. No independent split controls
or global flip absorption are claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- One transported positive E2 anchor for every one-split
makes the entire leaf lexicographic order, and hence BOTH
Devlin marker-1 and marker-2 edges, induced under any
bounded finite genuine diary leaf preembedding. -/
theorem finite_leafPreembedding_Devlin_of_positive_oneSplit_anchors
    {A B : Ordered3Graph Nat} {n k : Nat}
    {f : Nat → Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (DB : FiniteRoleDiaryBlock B k)
    (Q : FiniteLeafPreembedding A B n k f)
    (hAnchors : ∀ s : Nat, IsOneSplit A s →
      ∃ a : Nat, IsLeaf A a ∧ s < a ∧ a < n ∧
        A.edge 0 s a ∧ B.edge 0 (f s) (f a)) :
    ∀ u v : Nat, u < v → v < n →
      IsLeaf A u → IsLeaf A v →
      (A.edge 1 u v ↔ B.edge 1 (f u) (f v)) ∧
      (A.edge 2 u v ↔ B.edge 2 (f u) (f v)) := by
  intro u v huv hvn hu hv
  let m := A.oneMeetLevel u v
  have hm : IsOneSplit A m := DA.singleton_meets u v huv hvn hu hv
  have hmu : m < u := by
    have hle : m ≤ u := by
      have h := A.oneMeetLevel_le_min u v
      exact h.trans (min_le_left _ _)
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      have hOneU : IsOneSplit A u := by
        simpa only [heq] using hm
      exact hu.2.1 hOneU.2.1
  have hmv : m < v := lt_trans hmu huv
  have hmn : m < n := by omega
  have hun : u < n := by omega
  obtain ⟨a,ha,hma,han,hPositiveA,hPositiveB⟩ := hAnchors m hm
  have hE2 : A.edge 0 m v ↔ B.edge 0 (f m) (f v) :=
    finite_leafPreembedding_oneSplit_E2_of_positive_anchor
      DA.prediary DB.prediary Q m a hm ha hma han
      hPositiveA hPositiveB v hvn hv hmv
  have hBmu : IsOneSplit B (f m) :=
    ((Q.role_iff m hm.1 hmn).2.1).mpr hm
  have hBu : IsLeaf B (f u) :=
    ((Q.role_iff u hu.1 hun).1).mpr hu
  have hBv : IsLeaf B (f v) :=
    ((Q.role_iff v hv.1 hvn).1).mpr hv
  have hTargetMeet : B.oneMeetLevel (f u) (f v) = f m :=
    Q.leaf_oneMeet u v hu.1 hun hv.1 hvn hu hv
  have hSourceLex : LexEarlier A u v ↔ A.edge 0 m v :=
    E_oneSplit_lexEarlier_iff_right
      DA.prediary.permitted_edge m u v hm huv hmu rfl
  have hTargetLex :
      LexEarlier B (f u) (f v) ↔ B.edge 0 (f m) (f v) :=
    E_oneSplit_lexEarlier_iff_right
      DB.prediary.permitted_edge (f m) (f u) (f v)
      hBmu (Q.strictMono huv) (Q.strictMono hmu) hTargetMeet
  have hLex : LexEarlier A u v ↔ LexEarlier B (f u) (f v) :=
    hSourceLex.trans (hE2.trans hTargetLex.symm)
  have hOneA := DA.prediary.leaf_marker_one u v huv hvn hu hv
  have hTwoA := DA.prediary.leaf_marker_two u v huv hvn hu hv
  have hOneB :=
    DB.prediary.leaf_marker_one
      (f u) (f v) (Q.strictMono huv) (Q.image_bound v hvn) hBu hBv
  have hTwoB :=
    DB.prediary.leaf_marker_two
      (f u) (f v) (Q.strictMono huv) (Q.image_bound v hvn) hBu hBv
  exact ⟨hOneA.trans (hLex.trans hOneB.symm),
    hTwoA.trans ((not_congr hLex).trans hTwoB.symm)⟩

end DiaryLeafPriority
end ThreeUniformDiaries
