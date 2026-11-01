import ThreeUniformDiaries.DiaryFiniteUniversalLeafRange

/-!
# Track C: the concrete automorphism torsor of finite induced copies

A labelled finite induced copy has a specified map Fin n -> Nat, without
requiring that map to be increasing. Its image is the underlying
unlabelled copy. Two induced labelled copies with the SAME image
differ by a unique automorphism of the finite source.

This is the actual combinatorial reason for the |Aut(A)| factor in
the big Ramsey degree formula, rather than an assumed abstract label
set. It works for every finite 3-uniform hypergraph, not just diaries.

The ambient ordered graph is used only through the explicitly
symmetrised unordered hyperedge predicate. This does not classify
finite diary envelopes or prove an upper bound.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- A genuinely induced, labelled copy of a finite source, with no
restriction on the numerical order of the image labels. -/
def IsFiniteLabelledCopy
    (A K : Ordered3Graph Nat) (n : Nat)
    (v : Fin n → Nat) : Prop :=
  Function.Injective v ∧
    ∀ i j k : Fin n,
      A.unorderedEdge i.val j.val k.val ↔
        K.unorderedEdge (v i) (v j) (v k)

/-- Actual automorphisms of the finite unordered source, represented
as vertex permutations. The relation is tested for all triples,
using the symmetric irreflexive ternary edge predicate. -/
def FiniteHypergraphAut (A : Ordered3Graph Nat) (n : Nat) : Type :=
  { σ : Equiv.Perm (Fin n) //
      ∀ i j k : Fin n,
        A.unorderedEdge i.val j.val k.val ↔
          A.unorderedEdge (σ i).val (σ j).val (σ k).val }

noncomputable instance finiteHypergraphAutFintype
    (A : Ordered3Graph Nat) (n : Nat) :
    Fintype (FiniteHypergraphAut A n) := by
  classical
  unfold FiniteHypergraphAut
  infer_instance

/-- Re-labelling an induced copy by a genuine finite source
automorphism gives another induced labelled copy. -/
theorem finiteLabelledCopy_relabel
    {A K : Ordered3Graph Nat} {n : Nat}
    {v : Fin n → Nat}
    (hv : IsFiniteLabelledCopy A K n v)
    (σ : FiniteHypergraphAut A n) :
    IsFiniteLabelledCopy A K n (fun i => v (σ.val i)) := by
  refine ⟨hv.1.comp σ.val.injective, ?_⟩
  intro i j k
  exact (σ.property i j k).trans
    (hv.2 (σ.val i) (σ.val j) (σ.val k))

/-- Relabelling does not change the underlying vertex set. -/
theorem finiteLabelledCopy_relabel_range
    {A K : Ordered3Graph Nat} {n : Nat}
    (v : Fin n → Nat) (σ : FiniteHypergraphAut A n) :
    Set.range (fun i => v (σ.val i)) = Set.range v := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨σ.val i, rfl⟩
  · rintro ⟨i, rfl⟩
    refine ⟨σ.val.symm i, ?_⟩
    simp

/-- The exact automorphism torsor for an induced *unlabelled*
finite 3-hypergraph copy.

Given two embeddings of A with the same image, there is a unique
source automorphism σ such that w(i)=v(σ(i)) at every source vertex.
No ambient symmetry or homogeneity assumption is required. -/
theorem finiteLabelledCopy_unique_automorphism
    {A K : Ordered3Graph Nat} {n : Nat}
    {v w : Fin n → Nat}
    (hv : IsFiniteLabelledCopy A K n v)
    (hw : IsFiniteLabelledCopy A K n w)
    (hRange : Set.range v = Set.range w) :
    ∃! σ : FiniteHypergraphAut A n,
      ∀ i : Fin n, w i = v (σ.val i) := by
  classical
  have hWitness (i : Fin n) : ∃ j : Fin n, v j = w i := by
    have hmem : w i ∈ Set.range v := by
      rw [hRange]
      exact Set.mem_range_self i
    exact hmem
  let s : Fin n → Fin n := fun i => Classical.choose (hWitness i)
  have hs (i : Fin n) : v (s i) = w i :=
    Classical.choose_spec (hWitness i)
  have hinj : Function.Injective s := by
    intro i j hij
    apply hw.1
    calc
      w i = v (s i) := (hs i).symm
      _ = v (s j) := by rw [hij]
      _ = w j := hs j
  have hsurj : Function.Surjective s :=
    Finite.surjective_of_injective hinj
  let p : Equiv.Perm (Fin n) :=
    Equiv.ofBijective s ⟨hinj, hsurj⟩
  have hp (i : Fin n) : w i = v (p i) := by
    change w i = v (s i)
    exact (hs i).symm
  have hAut :
      ∀ i j k : Fin n,
        A.unorderedEdge i.val j.val k.val ↔
          A.unorderedEdge (p i).val (p j).val (p k).val := by
    intro i j k
    calc
      A.unorderedEdge i.val j.val k.val ↔
          K.unorderedEdge (w i) (w j) (w k) := hw.2 i j k
      _ ↔ K.unorderedEdge (v (p i)) (v (p j)) (v (p k)) := by
        rw [hp i, hp j, hp k]
      _ ↔ A.unorderedEdge (p i).val (p j).val (p k).val :=
        (hv.2 (p i) (p j) (p k)).symm
  let σ : FiniteHypergraphAut A n := ⟨p, hAut⟩
  refine ⟨σ, ?_, ?_⟩
  · intro i
    exact hp i
  · intro τ hτ
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply hv.1
    calc
      v (τ.val i) = w i := (hτ i).symm
      _ = v (σ.val i) := hp i

end Ordered3Graph
end ThreeUniformDiaries
