import ThreeUniformDiaries.DiaryFiniteAutTorsor

/-!
# Track B: exact size of a labelled-copy fibre over an unlabelled copy

The set of all induced labelled copies with one fixed unlabelled
image is a torsor for the automorphism group of the source.

Track C already proves that two such labelled copies differ by a
UNIQUE source automorphism. We package the exact statement as a
genuine equivalence of types and derive the corresponding Fintype
cardinality equality. This is the precise finite factor required
when converting the diary-copy palette to an embedding palette;
it is not an assumption that a generic label set happens to have
size |Aut(A)|.

No diary existence, Ramsey property or choice of a target diary
is used. The source is an arbitrary finite 3-uniform hypergraph,
and its edge predicate is interpreted symmetrically.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- All true labelled induced copies of A in K whose UNLABELLED
vertex image equals that of a prescribed embedding v. -/
def FiniteLabelledCopiesSameRange
    (A K : Ordered3Graph Nat) {n : Nat}
    (v : Fin n → Nat) : Type :=
  { w : Fin n → Nat //
      IsFiniteLabelledCopy A K n w ∧ Set.range w = Set.range v }

/-- A fixed labelled copy v identifies the entire fibre of
labelled embeddings over its unlabelled image with Aut(A).

The inverse uses the already proved UNIQUE automorphism theorem,
not an arbitrary permutation of the ambient target. -/
noncomputable def finiteHypergraphAut_equiv_sameRangeCopies
    {A K : Ordered3Graph Nat} {n : Nat}
    (v : Fin n → Nat)
    (hv : IsFiniteLabelledCopy A K n v) :
    FiniteHypergraphAut A n ≃ FiniteLabelledCopiesSameRange A K v := by
  classical
  let forward : FiniteHypergraphAut A n →
      FiniteLabelledCopiesSameRange A K v :=
    fun σ => ⟨fun i => v (σ.val i),
      finiteLabelledCopy_relabel hv σ,
      finiteLabelledCopy_relabel_range v σ⟩
  let backward : FiniteLabelledCopiesSameRange A K v →
      FiniteHypergraphAut A n :=
    fun w => Classical.choose
      (finiteLabelledCopy_unique_automorphism hv w.property.1
        w.property.2.symm)
  refine {
    toFun := forward
    invFun := backward
    left_inv := ?_
    right_inv := ?_
  }
  · intro σ
    change Classical.choose
        (finiteLabelledCopy_unique_automorphism hv
          (forward σ).property.1 (forward σ).property.2.symm) = σ
    have hUnique :=
      (Classical.choose_spec
        (finiteLabelledCopy_unique_automorphism hv
          (forward σ).property.1 (forward σ).property.2.symm)).2
    apply hUnique σ
    intro i
    rfl
  · intro w
    apply Subtype.ext
    funext i
    change v ((backward w).val i) = w.val i
    have hExists :=
      finiteLabelledCopy_unique_automorphism hv
        w.property.1 w.property.2.symm
    exact ((Classical.choose_spec hExists).1 i).symm

/-- The fibre is finite because the source automorphism group is
finite, even though the surrounding function space Fin n → Nat
is NOT finite. -/
noncomputable def finiteLabelledCopiesSameRangeFintype
    {A K : Ordered3Graph Nat} {n : Nat}
    (v : Fin n → Nat)
    (hv : IsFiniteLabelledCopy A K n v) :
    Fintype (FiniteLabelledCopiesSameRange A K v) :=
  Fintype.ofEquiv (FiniteHypergraphAut A n)
    (finiteHypergraphAut_equiv_sameRangeCopies v hv)

/-- EXACT cardinality of the labelled fibre, not merely an upper
bound or an abstract labelling factor. -/
theorem finiteLabelledCopiesSameRange_card_eq_aut
    {A K : Ordered3Graph Nat} {n : Nat}
    (v : Fin n → Nat)
    (hv : IsFiniteLabelledCopy A K n v) :
    letI : Fintype (FiniteLabelledCopiesSameRange A K v) :=
      finiteLabelledCopiesSameRangeFintype v hv
    Fintype.card (FiniteLabelledCopiesSameRange A K v) =
      Fintype.card (FiniteHypergraphAut A n) := by
  classical
  exact Fintype.card_congr
    (finiteHypergraphAut_equiv_sameRangeCopies v hv).symm

end Ordered3Graph
end ThreeUniformDiaries
