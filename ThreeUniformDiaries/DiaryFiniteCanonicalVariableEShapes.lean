import ThreeUniformDiaries.DiaryFiniteCanonicalFlipVariableEdges

/-!
# Genuine E-shapes where two canonical source flips can differ

Finite diary flips preserve the marker-defined role of each
vertex and the induced hypergraph of their common source leaves.
Thus all marker-role E1 edges and all leaf-only E5 edges are
literally fixed across the entire canonical source-flip orbit.

Each edge in a finite diary has one of five permitted E-shapes.
A differing edge in two genuine flips must therefore have one of
the remaining E2, E3 or E4 forms: an old one-split/leaf incidence,
a two-split/pair incidence, or a Devlin leaf-pair marker incidence.

This is a NECESSARY support classification, not a claim that
such edges are independent Boolean flip controls. In particular
the verified two-one-split coupling is not contradicted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Fliphood preserves the two actual marker-role edge bits on
every finite nonmarker vertex. No independent role flags. -/
theorem FiniteDiaryFlip.markerEdges_iff
    {A P : Ordered3Graph Nat} {n : Nat}
    (F : FiniteDiaryFlip A P n)
    (z : Nat) (hz3 : 3 ≤ z) (hzn : z < n) :
    (A.edge 0 1 z ↔ P.edge 0 1 z) ∧
    (A.edge 0 2 z ↔ P.edge 0 2 z) := by
  rcases F.source_diary.prediary.role_valid z hz3 hzn with
      hLeaf | hOne | hTwo
  · have hp : IsLeaf P z :=
      ((F.role_iff z hz3 hzn).1).mp hLeaf
    exact ⟨
      ⟨fun h => False.elim (hLeaf.2.1 h),
       fun h => False.elim (hp.2.1 h)⟩,
      ⟨fun h => False.elim (hLeaf.2.2 h),
       fun h => False.elim (hp.2.2 h)⟩⟩
  · have hp : IsOneSplit P z :=
      ((F.role_iff z hz3 hzn).2.1).mp hOne
    exact ⟨
      ⟨fun _ => hp.2.1,fun _ => hOne.2.1⟩,
      ⟨fun h => False.elim (hOne.2.2 h),
       fun h => False.elim (hp.2.2 h)⟩⟩
  · have hp : IsTwoSplit P z :=
      ((F.role_iff z hz3 hzn).2.2).mp hTwo
    exact ⟨
      ⟨fun h => False.elim (hTwo.2.1 h),
       fun h => False.elim (hp.2.1 h)⟩,
      ⟨fun _ => hp.2.2,fun _ => hTwo.2.2⟩⟩

/-- The actual E1 marker edges agree between ANY two genuine
finite flips of the same source diary. -/
theorem FiniteDiaryFlip.common_markerEdges_iff
    {A P Q : Ordered3Graph Nat} {n : Nat}
    (F : FiniteDiaryFlip A P n)
    (G : FiniteDiaryFlip A Q n)
    (z : Nat) (hz3 : 3 ≤ z) (hzn : z < n) :
    (P.edge 0 1 z ↔ Q.edge 0 1 z) ∧
    (P.edge 0 2 z ↔ Q.edge 0 2 z) := by
  have f := F.markerEdges_iff z hz3 hzn
  have g := G.markerEdges_iff z hz3 hzn
  exact ⟨f.1.symm.trans g.1, f.2.symm.trans g.2⟩

/-- The only permitted E shapes whose edges may vary across
genuine source flips; this definition does NOT declare that
their individual truth bits are independent. -/
def IsPossiblyVariableFiniteFlipEdge
    (A : Ordered3Graph Nat) (i j z : Nat) : Prop :=
  (i = 0 ∧ IsOneSplit A j ∧ IsLeaf A z) ∨
  (IsTwoSplit A i ∧ IsLeaf A j ∧ IsLeaf A z) ∨
  ((i = 1 ∨ i = 2) ∧ IsLeaf A j ∧ IsLeaf A z)

/-- If an increasing triple is an edge of one genuine flip but
not another, it has the source's E2, E3 or E4 shape.
E1 cannot change because marker-defined roles are preserved;
E5 cannot change because the leaf hypergraph is preserved. -/
theorem FiniteDiaryFlip.variable_shape_of_edge_difference
    {A P Q : Ordered3Graph Nat} {n : Nat}
    (F : FiniteDiaryFlip A P n)
    (G : FiniteDiaryFlip A Q n)
    (i j z : Fin n) (hij : i < j) (hjz : j < z)
    (hDifference : ¬ (P.edge i.val j.val z.val ↔
      Q.edge i.val j.val z.val))
    (hP : P.edge i.val j.val z.val) :
    IsPossiblyVariableFiniteFlipEdge A i.val j.val z.val := by
  rcases F.target_diary.prediary.permitted_edge
      i.val j.val z.val hP with
      hMarker | hOne | hTwo | hDevlin | hLeaf
  · obtain ⟨hi0,hj1or2,hz3⟩ := hMarker
    have hFixed := F.common_markerEdges_iff G
      z.val hz3 z.isLt
    have hSame : P.edge i.val j.val z.val ↔
        Q.edge i.val j.val z.val := by
      rcases hj1or2 with hj1 | hj2
      · simpa only [hi0,hj1] using hFixed.1
      · simpa only [hi0,hj2] using hFixed.2
    exact False.elim (hDifference hSame)
  · obtain ⟨hi0,hOneP,hLeafP⟩ := hOne
    have hOneA : IsOneSplit A j.val :=
      ((F.role_iff j.val hOneP.1 j.isLt).2.1).mpr hOneP
    have hLeafA : IsLeaf A z.val :=
      ((F.role_iff z.val hLeafP.1 z.isLt).1).mpr hLeafP
    exact Or.inl ⟨hi0,hOneA,hLeafA⟩
  · obtain ⟨hTwoP,hLeafJP,hLeafZP⟩ := hTwo
    have hTwoA : IsTwoSplit A i.val :=
      ((F.role_iff i.val hTwoP.1 i.isLt).2.2).mpr hTwoP
    have hLeafJA : IsLeaf A j.val :=
      ((F.role_iff j.val hLeafJP.1 j.isLt).1).mpr hLeafJP
    have hLeafZA : IsLeaf A z.val :=
      ((F.role_iff z.val hLeafZP.1 z.isLt).1).mpr hLeafZP
    exact Or.inr (Or.inl ⟨hTwoA,hLeafJA,hLeafZA⟩)
  · obtain ⟨hiMarker,hLeafJP,hLeafZP⟩ := hDevlin
    have hLeafJA : IsLeaf A j.val :=
      ((F.role_iff j.val hLeafJP.1 j.isLt).1).mpr hLeafJP
    have hLeafZA : IsLeaf A z.val :=
      ((F.role_iff z.val hLeafZP.1 z.isLt).1).mpr hLeafZP
    exact Or.inr (Or.inr ⟨hiMarker,hLeafJA,hLeafZA⟩)
  · obtain ⟨hLeafIP,hLeafJP,hLeafZP⟩ := hLeaf
    have hiA : IsLeaf A i.val :=
      ((F.role_iff i.val hLeafIP.1 i.isLt).1).mpr hLeafIP
    have hjA : IsLeaf A j.val :=
      ((F.role_iff j.val hLeafJP.1 j.isLt).1).mpr hLeafJP
    have hzA : IsLeaf A z.val :=
      ((F.role_iff z.val hLeafZP.1 z.isLt).1).mpr hLeafZP
    have heP := F.leaf_edge_iff
      i.val j.val z.val hij hjz z.isLt hiA hjA hzA
    have heQ := G.leaf_edge_iff
      i.val j.val z.val hij hjz z.isLt hiA hjA hzA
    exact False.elim (hDifference (heP.symm.trans heQ))

/-- Two finite source flips with different incidence at some
increasing triple must differ at an E2/E3/E4 source shape. -/
theorem FiniteDiaryFlip.variable_shape_of_difference
    {A P Q : Ordered3Graph Nat} {n : Nat}
    (F : FiniteDiaryFlip A P n)
    (G : FiniteDiaryFlip A Q n)
    (i j z : Fin n) (hij : i < j) (hjz : j < z)
    (hDifference : ¬ (P.edge i.val j.val z.val ↔
      Q.edge i.val j.val z.val)) :
    IsPossiblyVariableFiniteFlipEdge A i.val j.val z.val := by
  by_cases he : P.edge i.val j.val z.val
  · exact F.variable_shape_of_edge_difference
      G i j z hij hjz hDifference he
  · have hq : Q.edge i.val j.val z.val := by
      by_contra hq
      exact hDifference (iff_of_false he hq)
    exact G.variable_shape_of_edge_difference
      F i j z hij hjz (fun hh => hDifference hh.symm) hq

/-- Every two DISTINCT canonical codes in the true source flip
orbit differ at a GENUINE increasing triple with one of the
three potentially variable E2/E3/E4 shapes. -/
theorem canonical_source_flips_ne_variable_edge_shape
    (A : Ordered3Graph Nat) (n : Nat)
    (c d : FiniteDiaryEdgeCode n)
    (hc : c ∈ finiteCanonicalSourceFlipCodes A n)
    (hd : d ∈ finiteCanonicalSourceFlipCodes A n)
    (hne : c ≠ d) :
    ∃ i j z : Fin n, i < j ∧ j < z ∧
      IsPossiblyVariableFiniteFlipEdge A i.val j.val z.val ∧
      c i j z ≠ d i j z := by
  let P := finiteDiaryCodeGraph n c
  let Q := finiteDiaryCodeGraph n d
  have hRawC : c ∈ finiteSourceFlipCodes A n :=
    ((mem_finiteCanonicalSourceFlipCodes_iff A n c).mp hc).1
  have hRawD : d ∈ finiteSourceFlipCodes A n :=
    ((mem_finiteCanonicalSourceFlipCodes_iff A n d).mp hd).1
  have FC : FiniteDiaryFlip A P n :=
    (mem_finiteSourceFlipCodes_iff A n c).mp hRawC
  have FD : FiniteDiaryFlip A Q n :=
    (mem_finiteSourceFlipCodes_iff A n d).mp hRawD
  obtain ⟨i,j,z,hij,hjz,hDifferent⟩ :=
    (canonical_source_codes_ne_iff_increasing_witness
      A n c d hc hd).mp hne
  have heP : P.edge i.val j.val z.val ↔ c i j z = true := by
    constructor
    · rintro ⟨ha,hb,hz,hab,hbc,hbit⟩
      simpa using hbit
    · intro hbit
      exact ⟨i.isLt,j.isLt,z.isLt,hij,hjz,by simpa using hbit⟩
  have heQ : Q.edge i.val j.val z.val ↔ d i j z = true := by
    constructor
    · rintro ⟨ha,hb,hz,hab,hbc,hbit⟩
      simpa using hbit
    · intro hbit
      exact ⟨i.isLt,j.isLt,z.isLt,hij,hjz,by simpa using hbit⟩
  have hGraphDiff :
      ¬ (P.edge i.val j.val z.val ↔ Q.edge i.val j.val z.val) := by
    intro hEquiv
    have hTruth : (c i j z = true) ↔ (d i j z = true) :=
      heP.symm.trans (hEquiv.trans heQ)
    have hEq : c i j z = d i j z := by
      cases hC : c i j z <;>
        cases hD : d i j z <;>
        simp_all
    exact hDifferent hEq
  refine ⟨i,j,z,hij,hjz,?_,hDifferent⟩
  exact FC.variable_shape_of_difference FD
    i j z hij hjz hGraphDiff

end DiaryLeafPriority
end ThreeUniformDiaries
