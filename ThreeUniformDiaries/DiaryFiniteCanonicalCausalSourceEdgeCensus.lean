import ThreeUniformDiaries.DiaryFiniteCanonicalCausalRoleCensus
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalVTwoCoherence

/-!
# Source-branch witnesses for every non-Devlin edge of the causal graph

The actual causal marker extension adds NEW edges only with first
numerical coordinate 1 or 2. Every edge with first coordinate 0,
or with first coordinate at a genuine 1-/2-split, must already be
present in the indexed RAW sign-rooted relational union.

Unpack an arbitrary edge of this RAW union: its three vertices
are the images, under the verified finite predecessor-count
enumeration, of a genuine increasing source triple from SOME
canonical flip branch. This witnesses its full induced source
edge data, not merely a positive abstract Boolean table.

The zero-rank node is exactly the common original marker 0;
no positive source-level vertex can occupy numerical index zero.
Thus every completed zero-first-coordinate edge has an actual
source witness beginning with marker 0, a useful input for the
global V1 positive-incidence census. The analogous non-Devlin
statement is the input for global V2 coherence.

No completed global V1/V2 or absorber theorem is asserted here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Literal causal marker completion cannot alter any
edge whose first coordinate is neither marker 1 nor marker 2. -/
theorem finiteCanonicalCausalMarkerGraph_edge_iff_raw_of_nonDevlin
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (x y z : Nat)
    (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    (finiteCanonicalCausalMarkerGraph DA).edge x y z ↔
      (finiteCanonicalRankedRawGraph DA).edge x y z := by
  have h := causalMarkerLimit_formula
    (finiteCanonicalRankedRawGraph DA)
    (finiteCanonicalRankedOffBranchMask DA)
    (finiteCanonicalRankedOffBranchMask_later DA) x y z
  simpa [finiteCanonicalCausalMarkerGraph,
    CausalMarkerColumn,hx1,hx2] using h

/-- Every actual RAW edge in the finite ranked sign-rooted
union has an explicit source-branch representation preserving
its original increasing triple and genuine edge incidence. -/
theorem finiteCanonicalRankedRawGraph_edge_source_witness
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (x y z : Nat)
    (he : (finiteCanonicalRankedRawGraph DA).edge x y z) :
    ∃ (i : FiniteCanonicalFlipIndex A n)
      (a b c : Nat),
      a < b ∧ b < c ∧ c < n ∧
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i a (by omega))).val = x ∧
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i b (by omega))).val = y ∧
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i c (by omega))).val = z ∧
      ((finiteCanonicalSignRootedFamily DA).graph i).edge a b c := by
  rcases he with ⟨X,Y,Z,hX,hY,hZ,hEdge⟩
  rcases hEdge with ⟨i,a,b,c,hab,hbc,hcn,hNa,hNb,hNc,hSrc⟩
  have hXa : X = finiteCanonicalNodeAt DA i a (by omega) :=
    Subtype.ext hNa.symm
  have hYb : Y = finiteCanonicalNodeAt DA i b (by omega) :=
    Subtype.ext hNb.symm
  have hZc : Z = finiteCanonicalNodeAt DA i c hcn :=
    Subtype.ext hNc.symm
  refine ⟨i,a,b,c,hab,hbc,hcn,?_,?_,?_,hSrc⟩
  · simpa only [← hXa] using hX
  · simpa only [← hYb] using hY
  · simpa only [← hZc] using hZ

/-- In every canonical source branch, numerical rank zero is
occupied by its original marker-zero vertex and NOTHING ELSE. -/
theorem finiteCanonicalNodeAt_rank_zero_iff
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (a : Nat) (han : a < n) :
    (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i a han)).val = 0 ↔
      a = 0 := by
  constructor
  · intro hRank
    by_contra ha
    have h0a : 0 < a := by omega
    have hn : 3 ≤ n := DA.prediary.frame.length_ge_three
    have hlt := finiteCanonicalNodeAt_index_lt
      DA i 0 a h0a han
    have hzero : (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i 0 (by omega))).val = 0 :=
      finiteCanonicalMarker_zero_rank DA i
    omega
  · intro h
    subst a
    exact finiteCanonicalMarker_zero_rank DA i

/-- An edge of the completed graph beginning at marker 0
comes from a genuine positive source triple beginning at
the original marker 0, on SOME canonical flip branch.
Both remaining indexed endpoints are exactly represented. -/
theorem finiteCanonicalCausalMarkerGraph_zero_edge_source_witness
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (y z : Nat)
    (he : (finiteCanonicalCausalMarkerGraph DA).edge 0 y z) :
    ∃ (i : FiniteCanonicalFlipIndex A n)
      (b c : Nat),
      0 < b ∧ b < c ∧ c < n ∧
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i b (by omega))).val = y ∧
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i c (by omega))).val = z ∧
      ((finiteCanonicalSignRootedFamily DA).graph i).edge 0 b c := by
  have hRaw :
      (finiteCanonicalRankedRawGraph DA).edge 0 y z :=
    (finiteCanonicalCausalMarkerGraph_edge_iff_raw_of_nonDevlin
      DA 0 y z (by omega) (by omega)).mp he
  obtain ⟨i,a,b,c,hab,hbc,hcn,hX,hY,hZ,hSrc⟩ :=
    finiteCanonicalRankedRawGraph_edge_source_witness
      DA 0 y z hRaw
  have ha0 : a = 0 :=
    (finiteCanonicalNodeAt_rank_zero_iff DA i a (by omega)).mp hX
  subst a
  exact ⟨i,b,c,hab,hbc,hcn,hY,hZ,hSrc⟩

/-- A positive edge whose first vertex is not a Devlin marker
has its entire source-branch edge table and rank coordinates
available for the global positive-class coherence proof. -/
theorem finiteCanonicalCausalMarkerGraph_nonDevlin_source_witness
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (x y z : Nat)
    (hx1 : x ≠ 1) (hx2 : x ≠ 2)
    (he : (finiteCanonicalCausalMarkerGraph DA).edge x y z) :
    ∃ (i : FiniteCanonicalFlipIndex A n)
      (a b c : Nat),
      a < b ∧ b < c ∧ c < n ∧
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i a (by omega))).val = x ∧
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i b (by omega))).val = y ∧
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i c (by omega))).val = z ∧
      ((finiteCanonicalSignRootedFamily DA).graph i).edge a b c := by
  exact finiteCanonicalRankedRawGraph_edge_source_witness DA x y z
    ((finiteCanonicalCausalMarkerGraph_edge_iff_raw_of_nonDevlin
      DA x y z hx1 hx2).mp he)

end DiaryLeafPriority
end ThreeUniformDiaries
