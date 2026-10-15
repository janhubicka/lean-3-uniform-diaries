import ThreeUniformDiaries.DiaryPrediaryOneClassInsertion
import ThreeUniformDiaries.DiaryPrediaryTwoClassInsertion
import ThreeUniformDiaries.DiaryPrediaryClassIndicators

/-!
# Verification of V1/V2 coherence at newly inserted diary splits

The pre-diary insertion construction selects one OLD 1-type
(respectively full 2-type) class at ell+1 and adds all positive
incidences with a new split at ell.

We show that any two positive incidences at that new split
already agree as singleton (respectively full ordered-pair)
types at ell in the new graph. This is precisely the new
split's COHERENCE axiom, for arbitrary old leaves and ordered
leaf pairs.

Old shifted splits, the witness axioms, V3 lexicographic
coherence, allowed edge forms, and S1/S2 repair still need
the separate pre-diary insertion theorem.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- V1 coherence at the newly inserted 1-split, for any
two old leaves receiving its positive incidence. -/
theorem insertOneClass_new_oneSplit_coherent
    (H : Ordered3Graph Nat) (ell anchor u v : Nat)
    (hell : 3 ≤ ell)
    (hEllU : ell ≤ u) (hEllV : ell ≤ v)
    (hu : DiaryLeafPriority.IsLeaf H u)
    (hv : DiaryLeafPriority.IsLeaf H v)
    (heu : (H.insertOneClass ell anchor).edge
       0 ell (insertShift ell u))
    (hev : (H.insertOneClass ell anchor).edge
       0 ell (insertShift ell v)) :
    (H.insertOneClass ell anchor).SameOneTypeBelow
       ell (insertShift ell u) (insertShift ell v) := by
  have hAU : H.SameOneTypeBelow (ell+1) anchor u :=
    (H.insertOneClass_edge_iff ell anchor u hell hEllU hu).mp heu
  have hAV : H.SameOneTypeBelow (ell+1) anchor v :=
    (H.insertOneClass_edge_iff ell anchor v hell hEllV hv).mp hev
  have hUVnext : H.SameOneTypeBelow (ell+1) u v :=
    H.oneTypeBelow_trans (ell+1) u anchor v
      (H.oneTypeBelow_symm (ell+1) anchor u hAU) hAV
  have hUV : H.SameOneTypeBelow ell u v := by
    intro x y hxy hy
    exact hUVnext hxy (by omega)
  exact (H.insertWithNewEdges_oneTypeBelow_iff ell
    (H.oneClassExtra ell anchor) u v).mp hUV

/-- V2 coherence at the newly inserted 2-split,
for any two ordered old leaf pairs receiving its positive edge. -/
theorem insertTwoClass_new_twoSplit_coherent
    (H : Ordered3Graph Nat)
    (ell anchor₀ anchor₁ u v w x : Nat)
    (hell : 3 ≤ ell)
    (hEllU : ell < u) (hUV : u < v)
    (hEllW : ell < w) (hWX : w < x)
    (hu : DiaryLeafPriority.IsLeaf H u)
    (hv : DiaryLeafPriority.IsLeaf H v)
    (hw : DiaryLeafPriority.IsLeaf H w)
    (hx : DiaryLeafPriority.IsLeaf H x)
    (heu : (H.insertTwoClass ell anchor₀ anchor₁).edge
      ell (insertShift ell u) (insertShift ell v))
    (hew : (H.insertTwoClass ell anchor₀ anchor₁).edge
      ell (insertShift ell w) (insertShift ell x)) :
    (H.insertTwoClass ell anchor₀ anchor₁).SameTwoTypeBelow
      ell (insertShift ell u) (insertShift ell v)
      (insertShift ell w) (insertShift ell x) := by
  have hAU : H.SameTwoTypeBelow (ell+1)
      anchor₀ anchor₁ u v :=
    (H.insertTwoClass_edge_iff ell anchor₀ anchor₁
      u v hell hEllU hUV hu hv).mp heu
  have hAW : H.SameTwoTypeBelow (ell+1)
      anchor₀ anchor₁ w x :=
    (H.insertTwoClass_edge_iff ell anchor₀ anchor₁
      w x hell hEllW hWX hw hx).mp hew
  have hUVnext : H.SameTwoTypeBelow (ell+1) u v w x :=
    H.twoTypeBelow_trans (ell+1) u v anchor₀ anchor₁ w x
      (H.twoTypeBelow_symm (ell+1) anchor₀ anchor₁ u v hAU)
      hAW
  have hUV : H.SameTwoTypeBelow ell u v w x := by
    rcases hUVnext with ⟨h0, h1, hAux⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a b hab hb
      exact h0 hab (by omega)
    · intro a b hab hb
      exact h1 hab (by omega)
    · intro a ha
      exact hAux (by omega)
  exact (H.insertWithNewEdges_twoTypeBelow_iff ell
    (H.twoClassExtra ell anchor₀ anchor₁) u v w x).mp hUV

end Ordered3Graph
end ThreeUniformDiaries
