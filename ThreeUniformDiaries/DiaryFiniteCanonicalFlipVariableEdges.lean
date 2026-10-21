import ThreeUniformDiaries.DiaryFiniteCanonicalIncreasingSeparation
import ThreeUniformDiaries.DiaryFiniteFlipFirstDirection

/-!
# The variable edge coordinates of a genuine canonical source flip

Every finite diary flip preserves the induced hypergraph on its
genuine leaves. In particular, all canonical representatives of
the same source flip orbit AGREE on every increasing triple of
source leaves. These fixed incidences cannot separate two source
flip codes, regardless of the chosen canonical representation.

Combining exact canonical increasing-triple separation (#815) with
literal preservation of leaf-only edges proves that any two
distinct canonical source flips differ at an increasing triple
with AT LEAST ONE NONLEAF coordinate.

This makes the next geometric challenge more precise: source flip
separation must ultimately use genuine split/marker interactions,
not permanent leaf-only hypergraph edges. It does not assume that
all nonleaf coordinates are independent flip controls.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Equality of the truth value of a Boolean is enough to recover
the Boolean itself. -/
private theorem bool_eq_of_true_iff (x y : Bool)
    (h : (x = true) ↔ (y = true)) : x = y := by
  cases x <;> cases y <;> simp_all

/-- At genuine ordered source-leaf triples, all canonical flip
codes of the same source diary have exactly the SAME incidence
bit. This is independent of which noncanonical raw code originally
represented the flip. -/
theorem canonical_source_flips_agree_on_leaf_triples
    (A : Ordered3Graph Nat) (n : Nat)
    (c d : FiniteDiaryEdgeCode n)
    (hc : c ∈ finiteCanonicalSourceFlipCodes A n)
    (hd : d ∈ finiteCanonicalSourceFlipCodes A n)
    (i j z : Fin n) (hij : i < j) (hjz : j < z)
    (hi : IsLeaf A i.val) (hj : IsLeaf A j.val)
    (hz : IsLeaf A z.val) :
    c i j z = d i j z := by
  have hRawC : c ∈ finiteSourceFlipCodes A n :=
    ((mem_finiteCanonicalSourceFlipCodes_iff A n c).mp hc).1
  have hRawD : d ∈ finiteSourceFlipCodes A n :=
    ((mem_finiteCanonicalSourceFlipCodes_iff A n d).mp hd).1
  have FC : FiniteDiaryFlip A (finiteDiaryCodeGraph n c) n :=
    (mem_finiteSourceFlipCodes_iff A n c).mp hRawC
  have FD : FiniteDiaryFlip A (finiteDiaryCodeGraph n d) n :=
    (mem_finiteSourceFlipCodes_iff A n d).mp hRawD
  have hDecodeC :
      (finiteDiaryCodeGraph n c).edge i.val j.val z.val ↔
        c i j z = true := by
    constructor
    · rintro ⟨hiBound,hjBound,hzBound,_hij,_hjz,hBit⟩
      simpa using hBit
    · intro hBit
      exact ⟨i.isLt,j.isLt,z.isLt,hij,hjz,by simpa using hBit⟩
  have hDecodeD :
      (finiteDiaryCodeGraph n d).edge i.val j.val z.val ↔
        d i j z = true := by
    constructor
    · rintro ⟨hiBound,hjBound,hzBound,_hij,_hjz,hBit⟩
      simpa using hBit
    · intro hBit
      exact ⟨i.isLt,j.isLt,z.isLt,hij,hjz,by simpa using hBit⟩
  have hLeafC := FC.leaf_edge_iff
    i.val j.val z.val hij hjz z.isLt hi hj hz
  have hLeafD := FD.leaf_edge_iff
    i.val j.val z.val hij hjz z.isLt hi hj hz
  have hTruth : (c i j z = true) ↔ (d i j z = true) :=
    hDecodeC.symm.trans (hLeafC.symm.trans
      (hLeafD.trans hDecodeD))
  exact bool_eq_of_true_iff (c i j z) (d i j z) hTruth

/-- Distinct canonical source flips MUST differ at a genuine
increasing edge with a source coordinate which is not a leaf.
In particular invariant leaf-only hyperedges cannot witness
their distinction. -/
theorem canonical_source_flips_ne_has_nonleaf_edge_witness
    (A : Ordered3Graph Nat) (n : Nat)
    (c d : FiniteDiaryEdgeCode n)
    (hc : c ∈ finiteCanonicalSourceFlipCodes A n)
    (hd : d ∈ finiteCanonicalSourceFlipCodes A n)
    (hne : c ≠ d) :
    ∃ i j z : Fin n, i < j ∧ j < z ∧
      (¬ IsLeaf A i.val ∨ ¬ IsLeaf A j.val ∨
        ¬ IsLeaf A z.val) ∧ c i j z ≠ d i j z := by
  obtain ⟨i,j,z,hij,hjz,hDiff⟩ :=
    (canonical_source_codes_ne_iff_increasing_witness
      A n c d hc hd).mp hne
  refine ⟨i,j,z,hij,hjz,?_,hDiff⟩
  by_contra hAllLeaf
  have hi : IsLeaf A i.val := by
    by_contra h
    exact hAllLeaf (Or.inl h)
  have hj : IsLeaf A j.val := by
    by_contra h
    exact hAllLeaf (Or.inr (Or.inl h))
  have hz : IsLeaf A z.val := by
    by_contra h
    exact hAllLeaf (Or.inr (Or.inr h))
  exact hDiff (canonical_source_flips_agree_on_leaf_triples
    A n c d hc hd i j z hij hjz hi hj hz)

end DiaryLeafPriority
end ThreeUniformDiaries
