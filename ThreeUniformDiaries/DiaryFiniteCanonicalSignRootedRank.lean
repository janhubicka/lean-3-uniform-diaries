import ThreeUniformDiaries.DiaryFiniteSignRootedOrderedMaskCoherence

/-!
# Consecutive rank indices for the actual finite sign-rooted carrier

The canonical sign-rooted raw node carrier is finite but its
elements were ordered only by a strict total relation: source
level first, arbitrary injective tie rank second.

Assign every realised node X the number of carrier nodes Y
which precede X. This gives an explicit finite-valued rank
which is STRICTLY increasing under the verified level-first
total order, and therefore injective. The rank is bounded by
the number of actual carrier nodes and can be used as a
Nat-valued index in the literal causal-marker construction.

This is the numerical enumeration prerequisite. No new diary
edge predicates or absorber property are asserted here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The genuine finite set of realised carrier nodes before
a given node in the canonical level-first strict order. -/
noncomputable def finiteCanonicalNodePredecessors
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (X : FiniteCanonicalSignRootedVertex DA) :
    Finset (FiniteCanonicalSignRootedVertex DA) := by
  classical
  exact Finset.univ.filter (fun Y => finiteCanonicalNodeBefore DA Y X)

/-- A node belongs to the predecessor set iff it occurs
strictly before the chosen node in the actual finite order. -/
theorem finiteCanonicalNodePredecessors_mem_iff
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (X Y : FiniteCanonicalSignRootedVertex DA) :
    Y ∈ finiteCanonicalNodePredecessors DA X ↔
      finiteCanonicalNodeBefore DA Y X := by
  classical
  simp [finiteCanonicalNodePredecessors]

/-- The concrete enumeration rank is the number of predecessor
nodes in the finite canonical carrier. -/
noncomputable def finiteCanonicalNodeRank
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (X : FiniteCanonicalSignRootedVertex DA) : Nat :=
  (finiteCanonicalNodePredecessors DA X).card

/-- Whenever X precedes Y in the actual finite canonical
order, its rank is strictly smaller. -/
theorem finiteCanonicalNodeRank_lt_of_before
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    {X Y : FiniteCanonicalSignRootedVertex DA}
    (hXY : finiteCanonicalNodeBefore DA X Y) :
    finiteCanonicalNodeRank DA X < finiteCanonicalNodeRank DA Y := by
  classical
  have hSubset : finiteCanonicalNodePredecessors DA X ⊆
      finiteCanonicalNodePredecessors DA Y := by
    intro Z hZ
    apply (finiteCanonicalNodePredecessors_mem_iff DA Y Z).mpr
    exact finiteCanonicalNodeBefore_trans DA
      ((finiteCanonicalNodePredecessors_mem_iff DA X Z).mp hZ) hXY
  have hNe : finiteCanonicalNodePredecessors DA X ≠
      finiteCanonicalNodePredecessors DA Y := by
    intro hEq
    have hxY : X ∈ finiteCanonicalNodePredecessors DA Y :=
      (finiteCanonicalNodePredecessors_mem_iff DA Y X).mpr hXY
    have hxX : X ∈ finiteCanonicalNodePredecessors DA X := by
      rw [hEq]
      exact hxY
    exact (finiteCanonicalNodeBefore_irrefl DA X)
      ((finiteCanonicalNodePredecessors_mem_iff DA X X).mp hxX)
  exact Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨hSubset,hNe⟩)

/-- The rank function is injective on the ACTUAL finite node
carrier, not just on the ambient raw node type. -/
theorem finiteCanonicalNodeRank_injective
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    Function.Injective (finiteCanonicalNodeRank DA) := by
  intro X Y hRanks
  by_contra hXY
  rcases finiteCanonicalNodeBefore_total_of_ne DA X Y hXY with
      hBefore | hAfter
  · have hLt := finiteCanonicalNodeRank_lt_of_before DA hBefore
    omega
  · have hLt := finiteCanonicalNodeRank_lt_of_before DA hAfter
    omega

/-- The rank is genuinely bounded by the number of realised
carrier nodes; the chosen node cannot precede itself. -/
theorem finiteCanonicalNodeRank_lt_card
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (X : FiniteCanonicalSignRootedVertex DA) :
    finiteCanonicalNodeRank DA X <
      Fintype.card (FiniteCanonicalSignRootedVertex DA) := by
  classical
  have hSubset : finiteCanonicalNodePredecessors DA X ⊆
      (Finset.univ : Finset (FiniteCanonicalSignRootedVertex DA)) :=
    Finset.subset_univ _
  have hNe : finiteCanonicalNodePredecessors DA X ≠
      (Finset.univ : Finset (FiniteCanonicalSignRootedVertex DA)) := by
    intro hEq
    have hx : X ∈ finiteCanonicalNodePredecessors DA X := by
      rw [hEq]
      exact Finset.mem_univ _
    exact (finiteCanonicalNodeBefore_irrefl DA X)
      ((finiteCanonicalNodePredecessors_mem_iff DA X X).mp hx)
  have hCard := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨hSubset,hNe⟩)
  simpa only [finiteCanonicalNodeRank, Finset.card_univ] using hCard

/-- Each realised node now carries a well-defined index in
the consecutive finite initial segment. -/
noncomputable def finiteCanonicalNodeIndex
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (X : FiniteCanonicalSignRootedVertex DA) :
    Fin (Fintype.card (FiniteCanonicalSignRootedVertex DA)) :=
  ⟨finiteCanonicalNodeRank DA X,
    finiteCanonicalNodeRank_lt_card DA X⟩

theorem finiteCanonicalNodeIndex_injective
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    Function.Injective (finiteCanonicalNodeIndex DA) := by
  intro X Y h
  apply finiteCanonicalNodeRank_injective DA
  exact congrArg Fin.val h

/-- Indices are strictly increasing along the actual
level-first source and tie-broken canonical order. -/
theorem finiteCanonicalNodeIndex_lt_of_before
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    {X Y : FiniteCanonicalSignRootedVertex DA}
    (h : finiteCanonicalNodeBefore DA X Y) :
    (finiteCanonicalNodeIndex DA X).val <
      (finiteCanonicalNodeIndex DA Y).val :=
  finiteCanonicalNodeRank_lt_of_before DA h

/-- In particular, the rank increases with STRICTLY
increasing original source levels, independent of ties. -/
theorem finiteCanonicalNodeIndex_lt_of_source_lt
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (X Y : FiniteCanonicalSignRootedVertex DA)
    (h : X.val.1 < Y.val.1) :
    (finiteCanonicalNodeIndex DA X).val <
      (finiteCanonicalNodeIndex DA Y).val := by
  exact finiteCanonicalNodeIndex_lt_of_before DA
    (finiteCanonicalNodeBefore_of_level_lt DA X Y h)

end DiaryLeafPriority
end ThreeUniformDiaries
