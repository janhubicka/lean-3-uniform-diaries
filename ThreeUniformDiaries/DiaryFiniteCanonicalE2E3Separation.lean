import ThreeUniformDiaries.DiaryFiniteFlipDevlinSplitDependence
import ThreeUniformDiaries.DiaryFiniteCanonicalVariableEShapes

/-!
# Genuine source flip differences need only E2 and E3 witnesses

All real flip differences are in E2, E3 or E4 (#825). Every E4
Devlin leaf-pair marker is determined by the E2 incidence at
the pair's ORIGINAL singleton meet (#826). Thus an E4 difference
already forces an E2 difference. Consequently any two different
finite flips, and any two distinct canonical source codes, differ
on an E2 or an E3 edge.

This is an UNCONDITIONAL restriction on the true finite flip
orbit, not a claim that E2 and E3 bits can be chosen independently.
It removes redundant Devlin-marker comparisons from future finite
geometric-causality and pairwise separation checks.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The two remaining permitted source edge shapes which can
witness a genuine flip difference after Devlin-marker elimination. -/
def IsFiniteFlipE2OrE3Edge
    (A : Ordered3Graph Nat) (i j z : Nat) : Prop :=
  (i = 0 ∧ IsOneSplit A j ∧ IsLeaf A z) ∨
  (IsTwoSplit A i ∧ IsLeaf A j ∧ IsLeaf A z)

/-- Whenever genuine flips P and Q disagree on a source edge,
there is some (possibly different) increasing E2 or E3 source
edge on which they disagree. In the E4 case the replacement is
the E2 edge at the pair's actual singleton meet. -/
theorem FiniteDiaryFlip.difference_has_E2_or_E3_witness
    {A P Q : Ordered3Graph Nat} {n : Nat}
    (F : FiniteDiaryFlip A P n)
    (G : FiniteDiaryFlip A Q n)
    (i j z : Fin n) (hij : i < j) (hjz : j < z)
    (hDifferent : ¬ (P.edge i.val j.val z.val ↔
      Q.edge i.val j.val z.val)) :
    ∃ a b t : Fin n, a < b ∧ b < t ∧
      IsFiniteFlipE2OrE3Edge A a.val b.val t.val ∧
      ¬ (P.edge a.val b.val t.val ↔
        Q.edge a.val b.val t.val) := by
  rcases F.variable_shape_of_difference G
      i j z hij hjz hDifferent with hE2 | hE3 | hE4
  · exact ⟨i,j,z,hij,hjz,Or.inl hE2,hDifferent⟩
  · exact ⟨i,j,z,hij,hjz,Or.inr hE3,hDifferent⟩
  · obtain ⟨hMarker,hLeafJ,hLeafZ⟩ := hE4
    let m := A.oneMeetLevel j.val z.val
    have hmA : IsOneSplit A m :=
      F.source_diary.singleton_meets
        j.val z.val hjz z.isLt hLeafJ hLeafZ
    have hmle : m ≤ j.val := by
      have hBound := A.oneMeetLevel_le_min j.val z.val
      dsimp [m]
      omega
    have hmj : m < j.val := by
      by_contra hBad
      have hEq : m = j.val := by omega
      have hOneJ : IsOneSplit A j.val := by
        simpa only [hEq] using hmA
      exact hLeafJ.2.1 hOneJ.2.1
    have hmn : m < n := by omega
    have hZero : 0 < m := by
      have hThree := hmA.1
      omega
    have hNewDifferent :
        ¬ (P.edge 0 m z.val ↔ Q.edge 0 m z.val) :=
      F.devlin_difference_implies_oneSplit_difference
        G j.val z.val i.val hjz z.isLt
        hLeafJ hLeafZ hMarker hDifferent
    refine ⟨⟨0,by omega⟩,⟨m,hmn⟩,z,?_,?_,?_,?_⟩
    · change 0 < m
      exact hZero
    · change m < z.val
      omega
    · exact Or.inl ⟨rfl,hmA,hLeafZ⟩
    · exact hNewDifferent

/-- On a genuine increasing triple, decoding a canonical (or raw)
Boolean source edge table reads the same exact incidence bit. -/
private theorem decoded_edge_iff_bit_true
    (n : Nat) (c : FiniteDiaryEdgeCode n)
    (i j z : Fin n) (hij : i < j) (hjz : j < z) :
    (finiteDiaryCodeGraph n c).edge i.val j.val z.val ↔
      c i j z = true := by
  constructor
  · rintro ⟨_hi,_hj,_hz,_hij,_hjz,hbit⟩
    simpa using hbit
  · intro hbit
    exact ⟨i.isLt,j.isLt,z.isLt,hij,hjz,by simpa using hbit⟩

private theorem equal_true_iff_implies_equal
    (x y : Bool) (h : (x = true) ↔ (y = true)) :
    x = y := by
  cases x <;> cases y <;> simp_all

/-- Every distinct pair of actual canonical source-flip codes
differs on some strictly increasing E2 or E3 edge. In particular
Devlin E4 marker values need not be treated as separate coordinates
of the finite orbit. -/
theorem canonical_source_flips_ne_E2_or_E3_edge_witness
    (A : Ordered3Graph Nat) (n : Nat)
    (c d : FiniteDiaryEdgeCode n)
    (hc : c ∈ finiteCanonicalSourceFlipCodes A n)
    (hd : d ∈ finiteCanonicalSourceFlipCodes A n)
    (hne : c ≠ d) :
    ∃ a b t : Fin n, a < b ∧ b < t ∧
      IsFiniteFlipE2OrE3Edge A a.val b.val t.val ∧
      c a b t ≠ d a b t := by
  let P := finiteDiaryCodeGraph n c
  let Q := finiteDiaryCodeGraph n d
  have hRawC : c ∈ finiteSourceFlipCodes A n :=
    ((mem_finiteCanonicalSourceFlipCodes_iff A n c).mp hc).1
  have hRawD : d ∈ finiteSourceFlipCodes A n :=
    ((mem_finiteCanonicalSourceFlipCodes_iff A n d).mp hd).1
  have F : FiniteDiaryFlip A P n :=
    (mem_finiteSourceFlipCodes_iff A n c).mp hRawC
  have G : FiniteDiaryFlip A Q n :=
    (mem_finiteSourceFlipCodes_iff A n d).mp hRawD
  obtain ⟨i,j,z,hij,hjz,hInputNe⟩ :=
    (canonical_source_codes_ne_iff_increasing_witness
      A n c d hc hd).mp hne
  have hDiff : ¬ (P.edge i.val j.val z.val ↔
        Q.edge i.val j.val z.val) := by
    intro hGraph
    apply hInputNe
    have hTruth : (c i j z = true) ↔
        (d i j z = true) :=
      (decoded_edge_iff_bit_true n c i j z hij hjz).symm.trans
        (hGraph.trans
          (decoded_edge_iff_bit_true n d i j z hij hjz))
    exact equal_true_iff_implies_equal
      (c i j z) (d i j z) hTruth
  obtain ⟨a,b,t,hab,hbt,hShape,hEdgeNe⟩ :=
    F.difference_has_E2_or_E3_witness G
      i j z hij hjz hDiff
  refine ⟨a,b,t,hab,hbt,hShape,?_⟩
  intro hBitEq
  apply hEdgeNe
  have hTruth : (c a b t = true) ↔
      (d a b t = true) := by
    rw [hBitEq]
  exact (decoded_edge_iff_bit_true n c a b t hab hbt).trans
    (hTruth.trans
      (decoded_edge_iff_bit_true n d a b t hab hbt).symm)

end DiaryLeafPriority
end ThreeUniformDiaries
