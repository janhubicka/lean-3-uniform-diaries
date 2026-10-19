import ThreeUniformDiaries.DiaryFiniteLeafMeetRoleSupport
import Mathlib.Data.Finset.Sort

/-!
# Increasing reindexing of an arbitrary finite induced support

Given a finite set S of natural-number vertices, Mathlib's
Finset.orderEmbOfFin rfl enumerates S in strictly increasing
order. We extend this enumeration to an arbitrary Nat index
using a harmless default outside the finite cardinality.

The induced finite ternary graph has a new edge (a,b,c) exactly
when 0 <= a < b < c < |S| and the corresponding *actual*
old vertices form an edge. The finite range is therefore
literally induced (edges AND nonedges), with no accidental
outside edges. These elementary facts are independent of diary
axioms, role markers or meet closure and form the plumbing
for extraction of an actual finite diary from a leaf-meet support.

No claim that the restriction is already a finite diary is
made here: marker alignment, first-disagreement meets and
split witnesses are proved separately.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Increasing finite support enumeration; undefined indices
are assigned the harmless default 0 and cannot participate
in induced ordered edges. -/
noncomputable def finiteSupportIndex
    (S : Finset Nat) (i : Nat) : Nat :=
  if h : i < S.card then (S.orderEmbOfFin rfl) ⟨i,h⟩ else 0

/-- At a legitimate finite index, the map equals Mathlib's
increasing enumeration of the original support. -/
theorem finiteSupportIndex_of_lt
    (S : Finset Nat) (i : Nat) (hi : i < S.card) :
    finiteSupportIndex S i =
      (S.orderEmbOfFin rfl) ⟨i,hi⟩ := by
  simp only [finiteSupportIndex, dif_pos hi]

/-- Every selected finite index enumerates an ACTUAL old
vertex of the original support. -/
theorem finiteSupportIndex_mem
    (S : Finset Nat) (i : Nat) (hi : i < S.card) :
    finiteSupportIndex S i ∈ S := by
  rw [finiteSupportIndex_of_lt S i hi]
  exact Finset.orderEmbOfFin_mem S rfl ⟨i,hi⟩

/-- The finite index enumeration is strictly increasing on
its genuine domain; there are no collisions among indices. -/
theorem finiteSupportIndex_strictMono
    (S : Finset Nat) (i j : Nat)
    (hij : i < j) (hj : j < S.card) :
    finiteSupportIndex S i < finiteSupportIndex S j := by
  have hi : i < S.card := by omega
  have hFin : (⟨i,hi⟩ : Fin S.card) < ⟨j,hj⟩ := by
    exact hij
  have hStrict := (S.orderEmbOfFin rfl).strictMono hFin
  simpa only [finiteSupportIndex_of_lt S i hi,
    finiteSupportIndex_of_lt S j hj] using hStrict

/-- Every old supported vertex is enumerated by exactly SOME
finite index. This is the surjectivity needed to recover
old test coordinates when proving compressed meet equality. -/
theorem finiteSupportIndex_surjective_on
    (S : Finset Nat) (x : Nat) (hx : x ∈ S) :
    ∃ i : Nat, i < S.card ∧ finiteSupportIndex S i = x := by
  have hRange : Set.range (S.orderEmbOfFin rfl) = (S : Set Nat) :=
    Finset.range_orderEmbOfFin S rfl
  have hxRange : x ∈ Set.range (S.orderEmbOfFin rfl) := by
    rw [hRange]
    exact hx
  obtain ⟨i,hi⟩ := hxRange
  refine ⟨i.val,i.isLt,?_⟩
  simpa only [finiteSupportIndex_of_lt S i.val i.isLt] using hi

/-- Induced ternary graph on the increasing initial segment
indexed by S. All edges are restricted to genuine indices,
and the source relation is copied in BOTH directions. -/
noncomputable def finiteSupportGraph
    (G : Ordered3Graph Nat) (S : Finset Nat) :
    Ordered3Graph Nat where
  edge a b c :=
    a < b ∧ b < c ∧ c < S.card ∧
      G.edge (finiteSupportIndex S a)
        (finiteSupportIndex S b)
        (finiteSupportIndex S c)

/-- New edges have strictly increasing coordinates and their
largest coordinate is inside the finite cardinality. -/
theorem finiteSupportGraph_edge_ordered
    (G : Ordered3Graph Nat) (S : Finset Nat)
    (a b c : Nat)
    (he : (finiteSupportGraph G S).edge a b c) :
    a < b ∧ b < c ∧ c < S.card :=
  ⟨he.1,he.2.1,he.2.2.1⟩

/-- EXACT finite induced edge/nonedge reflection: for every
genuine increasing indexed triple, no new edge is created
and no original support edge is lost. -/
theorem finiteSupportGraph_edge_iff
    (G : Ordered3Graph Nat) (S : Finset Nat)
    (a b c : Nat) (hab : a < b)
    (hbc : b < c) (hc : c < S.card) :
    (finiteSupportGraph G S).edge a b c ↔
      G.edge (finiteSupportIndex S a)
        (finiteSupportIndex S b)
        (finiteSupportIndex S c) := by
  simp only [finiteSupportGraph, hab, hbc, hc,
    true_and]

end DiaryLeafPriority
end ThreeUniformDiaries
