import ThreeUniformDiaries.DiaryFiniteCanonicalCausalRoleCensus
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalVTwoCoherence

/-!
# Source-branch witnesses for non-Devlin edges of the causal graph

The causal extension inserts new edges only with first numerical
coordinate 1 or 2. Every edge whose first coordinate is zero
or a genuine source split must already occur in the ranked raw
sign-rooted relational union.

Each raw triple is represented on some canonical source flip
branch, at the exact original source coordinates. We package
the source coordinates as Fin n so their boundedness is available
inside the existential statement, instead of relying on a
conjunction to provide bounds to earlier terms.

This is an edge-source census; global V1/V2, witnesses and
general flip absorption are separate obligations.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The literal causal completion cannot add any edge whose
first vertex is not the Devlin marker 1 or 2. -/
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
    CausalMarkerColumn, hx1, hx2] using h

/-- Every raw edge admits an actual source-flip witness at
the same numerical indices, with all source coordinates
bounded by n and their genuine source edge incidence. -/
theorem finiteCanonicalRankedRawGraph_edge_source_witness
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (x y z : Nat)
    (he : (finiteCanonicalRankedRawGraph DA).edge x y z) :
    ∃ (i : FiniteCanonicalFlipIndex A n)
      (a b c : Fin n),
      a.val < b.val ∧ b.val < c.val ∧
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i a.val a.isLt)).val = x ∧
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i b.val b.isLt)).val = y ∧
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i c.val c.isLt)).val = z ∧
      ((finiteCanonicalSignRootedFamily DA).graph i).edge
        a.val b.val c.val := by
  rcases he with ⟨X,Y,Z,hX,hY,hZ,hEdge⟩
  rcases hEdge with ⟨i,a,b,c,hab,hbc,hcn,hNa,hNb,hNc,hSrc⟩
  have hXa : X = finiteCanonicalNodeAt DA i a (by omega) :=
    Subtype.ext hNa.symm
  have hYb : Y = finiteCanonicalNodeAt DA i b (by omega) :=
    Subtype.ext hNb.symm
  have hZc : Z = finiteCanonicalNodeAt DA i c hcn :=
    Subtype.ext hNc.symm
  refine ⟨i, ⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c,hcn⟩,
    hab,hbc,?_,?_,?_,hSrc⟩
  · simpa only [← hXa] using hX
  · simpa only [← hYb] using hY
  · simpa only [← hZc] using hZ

/-- Marker zero is the only vertex of rank zero in a
canonical source branch. -/
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

/-- Every edge of the completed graph starting with zero
is witnessed by an actual source-flip triple (0,b,c)
at the given numbered final vertices. -/
theorem finiteCanonicalCausalMarkerGraph_zero_edge_source_witness
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (y z : Nat)
    (he : (finiteCanonicalCausalMarkerGraph DA).edge 0 y z) :
    ∃ (i : FiniteCanonicalFlipIndex A n)
      (b c : Fin n),
      0 < b.val ∧ b.val < c.val ∧
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i b.val b.isLt)).val = y ∧
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i c.val c.isLt)).val = z ∧
      ((finiteCanonicalSignRootedFamily DA).graph i).edge
        0 b.val c.val := by
  have hRaw :
      (finiteCanonicalRankedRawGraph DA).edge 0 y z :=
    (finiteCanonicalCausalMarkerGraph_edge_iff_raw_of_nonDevlin
      DA 0 y z (by omega) (by omega)).mp he
  obtain ⟨i,a,b,c,hab,hbc,hX,hY,hZ,hSrc⟩ :=
    finiteCanonicalRankedRawGraph_edge_source_witness
      DA 0 y z hRaw
  have ha0 : a.val = 0 :=
    (finiteCanonicalNodeAt_rank_zero_iff DA i a.val a.isLt).mp hX
  have hzeroSource :
      ((finiteCanonicalSignRootedFamily DA).graph i).edge
        0 b.val c.val := by
    simpa only [ha0] using hSrc
  exact ⟨i,b,c,by omega,hbc,hY,hZ,hzeroSource⟩

/-- All non-Devlin completed edges have a fully bounded
source-branch witness; no new mixed E2/E3 edges arise. -/
theorem finiteCanonicalCausalMarkerGraph_nonDevlin_source_witness
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (x y z : Nat)
    (hx1 : x ≠ 1) (hx2 : x ≠ 2)
    (he : (finiteCanonicalCausalMarkerGraph DA).edge x y z) :
    ∃ (i : FiniteCanonicalFlipIndex A n)
      (a b c : Fin n),
      a.val < b.val ∧ b.val < c.val ∧
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i a.val a.isLt)).val = x ∧
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i b.val b.isLt)).val = y ∧
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i c.val c.isLt)).val = z ∧
      ((finiteCanonicalSignRootedFamily DA).graph i).edge
        a.val b.val c.val := by
  exact finiteCanonicalRankedRawGraph_edge_source_witness DA x y z
    ((finiteCanonicalCausalMarkerGraph_edge_iff_raw_of_nonDevlin
      DA x y z hx1 hx2).mp he)

end DiaryLeafPriority
end ThreeUniformDiaries
