import ThreeUniformDiaries.DiaryFiniteAlternatingRequiresTwoSplit

/-!
# Nine vertices are necessary for an alternating three-leaf gadget

If three leaves a<b<c of a complete finite diary share the same
singleton meet s on consecutive pairs, then the outer pair has a
strictly later meet u (a second one-split), and the V3/S2
pigeonhole lemma forces a distinct two-split t.

All six nonmarker objects t,s,u,a,b,c have different vertices
inside the genuine bounded diary frame. Thus the bound n is at
least nine. The explicit nine-vertex target smallFlipTarget
attains the bound.

This certifies optimality AMONG diaries containing this
particular alternating three-leaf gadget; it does not
establish minimality among all finite flip absorbers.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A finite complete diary with an alternating triple of leaves
at a common genuine 1-split has at least nine vertices.
The role and interval counting is explicit: three marker levels,
three different split vertices, and three genuine leaves. -/
theorem finite_three_leaf_alternation_requires_nine_vertices
    {H : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRoleDiaryBlock H n)
    (s a b c : Nat)
    (hs : IsOneSplit H s)
    (hsa : s < a) (hab : a < b) (hbc : b < c)
    (hcn : c < n)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c)
    (hAB : H.oneMeetLevel a b = s)
    (hBC : H.oneMeetLevel b c = s) :
    9 ≤ n := by
  classical
  obtain ⟨t,ht⟩ := finite_three_leaf_alternation_forces_twoSplit
    D s a b c hs hsa hab hbc hcn ha hb hc hAB hBC
  let u := H.oneMeetLevel a c
  have hOuter : s < u :=
    finite_three_leaf_outer_oneMeet_gt
      D.prediary s a b c hs hsa hab hbc hAB hBC
  have hOneU : IsOneSplit H u :=
    D.singleton_meets a c (lt_trans hab hbc) hcn ha hc
  have hUleA : u ≤ a := by
    have h := H.oneMeetLevel_le_min a c
    exact h.trans (min_le_left _ _)
  have hUneA : u ≠ a := by
    intro hEq
    have hOneA : IsOneSplit H a := by
      simpa only [hEq] using hOneU
    exact ha.2.1 hOneA.2.1
  have hUbeforeA : u < a := by omega
  have hT3 : 3 ≤ t := ht.1
  have hTltN : t < n := D.prediary.twoSplit_lt t ht
  have hTneS : t ≠ s := by
    intro hEq
    have hTwoS : IsTwoSplit H s := by
      simpa only [hEq] using ht
    exact hTwoS.2.1 hs.2.1
  have hTneU : t ≠ u := by
    intro hEq
    have hTwoU : IsTwoSplit H u := by
      simpa only [hEq] using ht
    exact hTwoU.2.1 hOneU.2.1
  have hTneA : t ≠ a := by
    intro hEq
    have hTwoA : IsTwoSplit H a := by
      simpa only [hEq] using ht
    exact ha.2.2 hTwoA.2.2
  have hTneB : t ≠ b := by
    intro hEq
    have hTwoB : IsTwoSplit H b := by
      simpa only [hEq] using ht
    exact hb.2.2 hTwoB.2.2
  have hTneC : t ≠ c := by
    intro hEq
    have hTwoC : IsTwoSplit H c := by
      simpa only [hEq] using ht
    exact hc.2.2 hTwoC.2.2
  by_contra hNine
  have hMax : n ≤ 8 := by omega
  have hS3 : 3 ≤ s := hs.1
  have hS : s = 3 := by omega
  have hU : u = 4 := by omega
  have hA : a = 5 := by omega
  have hB : b = 6 := by omega
  have hC : c = 7 := by omega
  have htCases : t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by
    omega
  rcases htCases with ht3 | ht4 | ht5 | ht6 | ht7
  · exact hTneS (by omega)
  · exact hTneU (by omega)
  · exact hTneA (by omega)
  · exact hTneB (by omega)
  · exact hTneC (by omega)

end DiaryLeafPriority
end ThreeUniformDiaries
