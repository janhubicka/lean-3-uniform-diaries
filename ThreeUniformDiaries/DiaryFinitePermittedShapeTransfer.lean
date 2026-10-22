import ThreeUniformDiaries.DiaryFiniteLeafPreembeddingComposition
import ThreeUniformDiaries.DiaryFullRoleDefinition

/-!
# Permitted E1--E5 edge shapes are invariant under finite leaf preembeddings

An order-preserving marker-fixing leaf preembedding already preserves
the ROLE of every genuine nonmarker source vertex. The five permitted
diary edge SHAPES therefore agree on every increasing finite source
triple, even though their actual E2/E3/Devlin incidences need not
yet agree.

This separates the simple structural classification from the
substantive positive-anchor E2/E3 column arguments and the
derived V3 marker transfers. It is useful in the final induced
pass of an anchored diary preembedding.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A strictly increasing map fixing the three markers sends
an input to a marker j<3 precisely if it was that marker. -/
theorem FiniteLeafPreembedding.marker_image_eq_iff
    {A B : Ordered3Graph Nat} {n k : Nat} {f : Nat → Nat}
    (Q : FiniteLeafPreembedding A B n k f)
    (u j : Nat) (hj : j < 3) :
    f u = j ↔ u = j := by
  have hFix : f j = j := by
    have hjCases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hjCases with rfl | rfl | rfl
    · exact Q.marker_zero
    · exact Q.marker_one
    · exact Q.marker_two
  constructor
  · intro hImage
    by_cases hu_lt : u < j
    · have hlt := Q.strictMono hu_lt
      rw [hFix,hImage] at hlt
      omega
    · by_cases hj_lt : j < u
      · have hlt := Q.strictMono hj_lt
        rw [hFix,hImage] at hlt
        omega
      · omega
  · intro h
    subst u
    exact hFix

/-- The three nonmarker role predicates are preserved and
reflected on every source vertex actually inside the bound;
the marker cases are automatic from marker fixing. -/
theorem FiniteLeafPreembedding.all_role_iff
    {A B : Ordered3Graph Nat} {n k : Nat} {f : Nat → Nat}
    (Q : FiniteLeafPreembedding A B n k f)
    (u : Nat) (hun : u < n) :
    (IsLeaf B (f u) ↔ IsLeaf A u) ∧
    (IsOneSplit B (f u) ↔ IsOneSplit A u) ∧
    (IsTwoSplit B (f u) ↔ IsTwoSplit A u) := by
  by_cases hu3 : 3 ≤ u
  · exact Q.role_iff u hu3 hun
  · have hMarker : u = 0 ∨ u = 1 ∨ u = 2 := by omega
    rcases hMarker with rfl | rfl | rfl
    · simp [Q.marker_zero,IsLeaf,IsOneSplit,IsTwoSplit]
    · simp [Q.marker_one,IsLeaf,IsOneSplit,IsTwoSplit]
    · simp [Q.marker_two,IsLeaf,IsOneSplit,IsTwoSplit]

/-- Source vertices are at level >=3 exactly when their
images lie beyond the three fixed markers. -/
theorem FiniteLeafPreembedding.image_ge_three_iff
    {A B : Ordered3Graph Nat} {n k : Nat} {f : Nat → Nat}
    (Q : FiniteLeafPreembedding A B n k f)
    (u : Nat) :
    3 ≤ f u ↔ 3 ≤ u := by
  constructor
  · intro hge
    by_contra hn
    have hCase : u = 0 ∨ u = 1 ∨ u = 2 := by omega
    rcases hCase with rfl | rfl | rfl
    · rw [Q.marker_zero] at hge
      omega
    · rw [Q.marker_one] at hge
      omega
    · rw [Q.marker_two] at hge
      omega
  · intro hge
    have hOrder := Q.strictMono (show 2 < u by omega)
    rw [Q.marker_two] at hOrder
    omega

/-- The permitted five E1--E5 shape predicates are equivalent
on every genuine source triple of any bounded leaf preembedding.
No actual nonmarker split edge is assumed to be preserved. -/
theorem FiniteLeafPreembedding.permittedEdge_iff
    {A B : Ordered3Graph Nat} {n k : Nat} {f : Nat → Nat}
    (Q : FiniteLeafPreembedding A B n k f)
    (a b c : Nat)
    (hab : a < b) (hbc : b < c) (hcn : c < n) :
    PermittedDiaryEdge A a b c ↔
      PermittedDiaryEdge B (f a) (f b) (f c) := by
  have han : a < n := by omega
  have hbn : b < n := by omega
  have hRoleA := Q.all_role_iff a han
  have hRoleB := Q.all_role_iff b hbn
  have hRoleC := Q.all_role_iff c hcn
  have hA0 := Q.marker_image_eq_iff a 0 (by omega)
  have hA1 := Q.marker_image_eq_iff a 1 (by omega)
  have hA2 := Q.marker_image_eq_iff a 2 (by omega)
  have hB1 := Q.marker_image_eq_iff b 1 (by omega)
  have hB2 := Q.marker_image_eq_iff b 2 (by omega)
  have hC3 := Q.image_ge_three_iff c
  simp only [PermittedDiaryEdge,hA0,hA1,hA2,hB1,hB2,hC3,
    hRoleA.1,hRoleA.2.2,hRoleB.1,hRoleB.2.1,hRoleC.1]

end DiaryLeafPriority
end ThreeUniformDiaries
