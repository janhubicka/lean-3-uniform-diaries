import ThreeUniformDiaries.DiaryFiniteCanonicalCausalMarkerGraph

/-!
# The three common sign-rooted markers have numerical ranks 0, 1, 2

The finite canonical sign-rooted carrier has a strict level-first order
whose numerical rank counts all preceding REALISED nodes. All genuine
source flips identify their three marker levels, so every realised
node of original level 0, 1 or 2 is unique.

Consequently the original distinguished vertices 0, 1 and 2
have precisely ranks 0, 1 and 2 in the full finite carrier,
regardless of the number of flips or the choice of tie rank.

This is essential to identify the literal Nat-indexed Devlin
marker equations with the original source marker incidence.
No claim about full pre-diary axioms or flip absorption is made.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The source level of an actual bounded canonical branch node. -/
@[simp] theorem finiteCanonicalNodeAt_level
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (z : Nat) (hzn : z < n) :
    (finiteCanonicalNodeAt DA i z hzn).val.1 = z := by
  exact (finiteCanonicalSignRootedFamily DA).node_level i z

/-- All actual finite nodes at a fixed marker level k<3 are literally
the SAME shared node, regardless of their source flip. -/
theorem finiteCanonicalMarker_unique_at_level
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (k : Nat) (hk3 : k < 3) (hkn : k < n)
    (Y : FiniteCanonicalSignRootedVertex DA)
    (hYlevel : Y.val.1 = k) :
    Y = finiteCanonicalNodeAt DA i k hkn := by
  classical
  have hmem : Y.val ∈ finiteCanonicalSignRootedNodeSet DA :=
    Y.property
  unfold finiteCanonicalSignRootedNodeSet at hmem
  obtain ⟨⟨j,t⟩, _, hEq⟩ := Finset.mem_image.mp hmem
  have ht : t.val = k := by
    have hh : t.val = Y.val.1 := by
      simpa only [FiniteSignRootedFlipFamily.node_level] using
        (congrArg Prod.fst hEq)
    omega
  apply Subtype.ext
  change Y.val = (finiteCanonicalSignRootedFamily DA).node i k
  calc
    Y.val = (finiteCanonicalSignRootedFamily DA).node j t.val :=
      hEq.symm
    _ = (finiteCanonicalSignRootedFamily DA).node j k := by rw [ht]
    _ = (finiteCanonicalSignRootedFamily DA).node i k :=
      (finiteCanonicalSignRootedFamily DA).node_markers_shared j i k hk3

/-- The unique source marker 0 precedes no actual finite carrier node:
its predecessor count, hence its numerical rank, is exactly zero. -/
theorem finiteCanonicalMarker_zero_rank
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n) :
    finiteCanonicalNodeRank DA
      (finiteCanonicalNodeAt DA i 0 (by
        have hn := DA.prediary.frame.length_ge_three
        omega)) = 0 := by
  classical
  have hn : 3 ≤ n := DA.prediary.frame.length_ge_three
  let m0 : FiniteCanonicalSignRootedVertex DA :=
    finiteCanonicalNodeAt DA i 0 (by omega)
  have hEmpty : finiteCanonicalNodePredecessors DA m0 = ∅ := by
    ext Y
    constructor
    · intro hY
      have hBefore : finiteCanonicalNodeBefore DA Y m0 :=
        (finiteCanonicalNodePredecessors_mem_iff DA m0 Y).mp hY
      have hm0 : m0.val.1 = 0 := by
        simp only [m0,finiteCanonicalNodeAt_level]
      have hYL : Y.val.1 = 0 := by
        rcases hBefore with hLt | ⟨hTie,_⟩ <;> omega
      have hEq : Y = m0 :=
        finiteCanonicalMarker_unique_at_level DA i 0 (by omega)
          (by omega) Y hYL
      rw [hEq] at hBefore
      exact False.elim ((finiteCanonicalNodeBefore_irrefl DA m0) hBefore)
    · intro hY
      have hFalse : False := by simpa using hY
      exact hFalse.elim
  change (finiteCanonicalNodePredecessors DA m0).card = 0
  rw [hEmpty]
  rfl

/-- Marker 1 has exactly one predecessor (the shared marker 0),
regardless of the finite flip orbit or the tie order. -/
theorem finiteCanonicalMarker_one_rank
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n) :
    finiteCanonicalNodeRank DA
      (finiteCanonicalNodeAt DA i 1 (by
        have hn := DA.prediary.frame.length_ge_three
        omega)) = 1 := by
  classical
  have hn : 3 ≤ n := DA.prediary.frame.length_ge_three
  let m0 : FiniteCanonicalSignRootedVertex DA :=
    finiteCanonicalNodeAt DA i 0 (by omega)
  let m1 : FiniteCanonicalSignRootedVertex DA :=
    finiteCanonicalNodeAt DA i 1 (by omega)
  have hSubset : finiteCanonicalNodePredecessors DA m1 ⊆ {m0} := by
    intro Y hY
    have hBefore : finiteCanonicalNodeBefore DA Y m1 :=
      (finiteCanonicalNodePredecessors_mem_iff DA m1 Y).mp hY
    have hm1 : m1.val.1 = 1 := by
      simp only [m1,finiteCanonicalNodeAt_level]
    have hBeforeOrig := hBefore
    have hYlt : Y.val.1 < 1 := by
      rcases hBefore with hLt | ⟨hTie,_⟩
      · omega
      · have hEq : Y = m1 :=
          finiteCanonicalMarker_unique_at_level DA i 1
            (by omega) (by omega) Y (by omega)
        rw [hEq] at hBeforeOrig
        exact False.elim ((finiteCanonicalNodeBefore_irrefl DA m1)
          hBeforeOrig)
    have hEq : Y = m0 :=
      finiteCanonicalMarker_unique_at_level DA i 0 (by omega)
        (by omega) Y (by omega)
    simpa [hEq]
  have hUpper : finiteCanonicalNodeRank DA m1 ≤ 1 := by
    have h := Finset.card_le_card hSubset
    simpa [finiteCanonicalNodeRank] using h
  have hBefore : finiteCanonicalNodeBefore DA m0 m1 :=
    finiteCanonicalNodeBefore_of_level_lt DA m0 m1 (by
      simp only [m0,m1,finiteCanonicalNodeAt_level]
      omega)
  have hLower := finiteCanonicalNodeRank_lt_of_before DA hBefore
  have hZero : finiteCanonicalNodeRank DA m0 = 0 :=
    finiteCanonicalMarker_zero_rank DA i
  change finiteCanonicalNodeRank DA m1 = 1
  omega

/-- Marker 2 has exactly two predecessors (markers 0 and 1).
Thus all three shared original markers retain their actual
numerical identities under the full canonical flip enumeration. -/
theorem finiteCanonicalMarker_two_rank
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n) :
    finiteCanonicalNodeRank DA
      (finiteCanonicalNodeAt DA i 2 (by
        have hn := DA.prediary.frame.length_ge_three
        omega)) = 2 := by
  classical
  have hn : 3 ≤ n := DA.prediary.frame.length_ge_three
  let m0 : FiniteCanonicalSignRootedVertex DA :=
    finiteCanonicalNodeAt DA i 0 (by omega)
  let m1 : FiniteCanonicalSignRootedVertex DA :=
    finiteCanonicalNodeAt DA i 1 (by omega)
  let m2 : FiniteCanonicalSignRootedVertex DA :=
    finiteCanonicalNodeAt DA i 2 (by omega)
  have hSubset : finiteCanonicalNodePredecessors DA m2 ⊆
      ({m0,m1} : Finset (FiniteCanonicalSignRootedVertex DA)) := by
    intro Y hY
    have hBefore : finiteCanonicalNodeBefore DA Y m2 :=
      (finiteCanonicalNodePredecessors_mem_iff DA m2 Y).mp hY
    have hm2 : m2.val.1 = 2 := by
      simp only [m2,finiteCanonicalNodeAt_level]
    have hBeforeOrig := hBefore
    have hYlt : Y.val.1 < 2 := by
      rcases hBefore with hLt | ⟨hTie,_⟩
      · omega
      · have hEq : Y = m2 :=
          finiteCanonicalMarker_unique_at_level DA i 2
            (by omega) (by omega) Y (by omega)
        rw [hEq] at hBeforeOrig
        exact False.elim ((finiteCanonicalNodeBefore_irrefl DA m2)
          hBeforeOrig)
    have hYcases : Y.val.1 = 0 ∨ Y.val.1 = 1 := by omega
    rcases hYcases with h0 | h1
    · have hEq : Y = m0 :=
        finiteCanonicalMarker_unique_at_level DA i 0
          (by omega) (by omega) Y h0
      simp [hEq]
    · have hEq : Y = m1 :=
        finiteCanonicalMarker_unique_at_level DA i 1
          (by omega) (by omega) Y h1
      simp [hEq]
  have hNe : m0 ≠ m1 := by
    intro heq
    have h := congrArg
      (fun X : FiniteCanonicalSignRootedVertex DA => X.val.1) heq
    simp only [m0,m1,finiteCanonicalNodeAt_level] at h
    omega
  have hUpper : finiteCanonicalNodeRank DA m2 ≤ 2 := by
    have h := Finset.card_le_card hSubset
    simpa [finiteCanonicalNodeRank,hNe] using h
  have hBefore : finiteCanonicalNodeBefore DA m1 m2 :=
    finiteCanonicalNodeBefore_of_level_lt DA m1 m2 (by
      simp only [m1,m2,finiteCanonicalNodeAt_level]
      omega)
  have hLower := finiteCanonicalNodeRank_lt_of_before DA hBefore
  have hOne : finiteCanonicalNodeRank DA m1 = 1 :=
    finiteCanonicalMarker_one_rank DA i
  change finiteCanonicalNodeRank DA m2 = 2
  omega

/-- In the Nat-indexed canonical sign-rooted graph, the three
common source marker vertices are LITERALLY at 0,1,2. -/
theorem finiteCanonicalMarker_indices_exact
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n) :
    (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i 0 (by
        have hn := DA.prediary.frame.length_ge_three
        omega))).val = 0 ∧
    (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i 1 (by
        have hn := DA.prediary.frame.length_ge_three
        omega))).val = 1 ∧
    (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i 2 (by
        have hn := DA.prediary.frame.length_ge_three
        omega))).val = 2 := by
  constructor
  · exact finiteCanonicalMarker_zero_rank DA i
  constructor
  · exact finiteCanonicalMarker_one_rank DA i
  · exact finiteCanonicalMarker_two_rank DA i

end DiaryLeafPriority
end ThreeUniformDiaries
