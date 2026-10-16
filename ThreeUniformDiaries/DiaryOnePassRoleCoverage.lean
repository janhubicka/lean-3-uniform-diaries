import ThreeUniformDiaries.DiaryOnePassIndexCoverage
import ThreeUniformDiaries.DiaryOnePassPermittedEdges

/-!
# All-role coverage and the complete E interface for the raw target

The concrete static one-pass target has only two sorts of vertices:
images of original vertices and actual inserted events. This fact is
the global finite-block index-coverage theorem (previous module).

For original vertices, all marker-defined roles are reflected and
preserved by the induced old copy. For fresh vertices, the event arity
determines the literal IsOneSplit or IsTwoSplit predicate, including
the absence of the opposite role marker.

We therefore prove role_valid for EVERY target vertex at or above 3.
Together with the already checked edge_ordered and full E1--E5
permitted edge classification, this yields the complete role/E
conjunction required by the pre-diary definition. It is a genuine
target structural theorem rather than an abstract finite code lemma.

V1/V2 coherence and witnesses, Devlin V3, S1/S2 and the global type
transport induction are not part of this statement.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every vertex of the raw one-pass target above the three markers
has exactly one of the manuscript's allowed roles, expressed by
ACTUAL target marker edges. -/
theorem onePassRawTarget_role_valid
    {H : Ordered3Graph Nat} (P : RolePrediary H) :
    ∀ v : Nat, 3 ≤ v →
      IsLeaf (onePassRawTarget H) v ∨
      IsOneSplit (onePassRawTarget H) v ∨
      IsTwoSplit (onePassRawTarget H) v := by
  intro v hv
  rcases onePass_target_index_covered H v with
      ⟨m, hm⟩ | ⟨m, i, hi⟩
  · have hOldThree : 3 ≤ onePassOldImage H m := by
      rw [hm]
      exact hv
    have hm3 : 3 ≤ m :=
      (onePassOldImage_ge_three_iff H m).mp hOldThree
    rcases P.role_valid m hm3 with hLeaf | hOne | hTwo
    · apply Or.inl
      have hOld :=
        (onePassRawTarget_old_leaf_iff H m).mpr hLeaf
      simpa only [hm] using hOld
    · apply Or.inr
      apply Or.inl
      have hOld :=
        (onePassRawTarget_old_oneSplit_iff H m).mpr hOne
      simpa only [hm] using hOld
    · apply Or.inr
      apply Or.inr
      have hOld :=
        (onePassRawTarget_old_twoSplit_iff H m).mpr hTwo
      simpa only [hm] using hOld
  · rcases onePass_event_label_at_own_cut H m i with
        ⟨g, hg⟩ | ⟨g, hg⟩
    · apply Or.inr
      apply Or.inr
      have hRole := onePassRawTarget_fresh_twoSplit H m i g hg
      simpa only [hi] using hRole
    · apply Or.inr
      apply Or.inl
      have hRole := onePassRawTarget_fresh_oneSplit H m i g hg
      simpa only [hi] using hRole

/-- All THREE structural E/role clauses of the manuscript's
pre-diary are satisfied by the concrete candidate:
(1) every vertex has a permitted marker role;
(2) all edges are increasing;
(3) every edge has one of exactly E1--E5 allowed shapes.

The remaining V and S axioms are not smuggled into this theorem. -/
theorem onePassRawTarget_role_and_E
    {H : Ordered3Graph Nat} (P : RolePrediary H) :
    (∀ v : Nat, 3 ≤ v →
      IsLeaf (onePassRawTarget H) v ∨
      IsOneSplit (onePassRawTarget H) v ∨
      IsTwoSplit (onePassRawTarget H) v) ∧
    (∀ x y z : Nat, (onePassRawTarget H).edge x y z →
      x < y ∧ y < z) ∧
    (∀ x y z : Nat, (onePassRawTarget H).edge x y z →
      PermittedDiaryEdge (onePassRawTarget H) x y z) := by
  refine ⟨onePassRawTarget_role_valid P, ?_, ?_⟩
  · intro x y z he
    exact onePassRawTarget_edge_ordered P x y z he
  · intro x y z he
    exact onePassRawTarget_permitted_edge P x y z he

end DiaryLeafPriority
end ThreeUniformDiaries
