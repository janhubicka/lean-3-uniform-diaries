import ThreeUniformDiaries.DiaryFiniteAutTorsor

/-!
# Track C: exact cardinality of the labelled-copy automorphism fibre

The merged finite-copy torsor theorem establishes unique relabelling
by an automorphism whenever two labelled induced copies have the same
unlabelled vertex set. Here we package that uniqueness as an explicit
equivalence of FINITE types. Thus every fibre of the map
  labelled induced copy -> unlabelled vertex set
has precisely |Aut(A)| elements.

This is independent of diary axioms, genericity, Ramsey theory,
and the unknown sharp finite marked-diary classification.
For the latter it can be specialised to the fibre over one
genuine finite diary source, once the correspondence of markings
with its leaf labellings has been established separately.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- All labelled induced copies of A in K having exactly the
same image as a prescribed map v. The ambient vertex carrier
need not be finite. -/
def FiniteLabelledCopyFibre
    (A K : Ordered3Graph Nat) (n : Nat)
    (v : Fin n → Nat) : Type :=
  { w : Fin n → Nat //
    IsFiniteLabelledCopy A K n w ∧
      Set.range w = Set.range v }

/-- Exact equivalence of the fibre of one genuine unlabelled
finite copy with the *actual* finite automorphism group of A.
The forward map relabels v by an automorphism; surjectivity
uses the uniqueness theorem, not any counting heuristic. -/
noncomputable def finiteLabelledCopyFibre_equiv_aut
    {A K : Ordered3Graph Nat} {n : Nat}
    {v : Fin n → Nat}
    (hv : IsFiniteLabelledCopy A K n v) :
    FiniteHypergraphAut A n ≃ FiniteLabelledCopyFibre A K n v := by
  classical
  let f : FiniteHypergraphAut A n →
      FiniteLabelledCopyFibre A K n v :=
    fun σ => ⟨(fun i => v (σ.val i)),
      finiteLabelledCopy_relabel hv σ,
      finiteLabelledCopy_relabel_range (A := A) (K := K) v σ⟩
  have hf_inj : Function.Injective f := by
    intro σ τ h
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply hv.1
    exact congrArg
      (fun W : FiniteLabelledCopyFibre A K n v => W.val i) h
  have hf_surj : Function.Surjective f := by
    intro W
    obtain ⟨σ, hσ, _⟩ :=
      finiteLabelledCopy_unique_automorphism
        hv W.property.1 W.property.2.symm
    refine ⟨σ, ?_⟩
    apply Subtype.ext
    funext i
    exact (hσ i).symm
  exact Equiv.ofBijective f ⟨hf_inj, hf_surj⟩

/-- A finite labelled-copy fibre is genuinely finite despite the
ambient target having countably many vertices. -/
noncomputable def finiteLabelledCopyFibre_fintype
    {A K : Ordered3Graph Nat} {n : Nat}
    {v : Fin n → Nat}
    (hv : IsFiniteLabelledCopy A K n v) :
    Fintype (FiniteLabelledCopyFibre A K n v) := by
  classical
  exact Fintype.ofEquiv (FiniteHypergraphAut A n)
    (finiteLabelledCopyFibre_equiv_aut hv)

/-- Concrete exact multiplier for every unlabelled copy: the
number of labelled copies on the very same image is |Aut(A)|.
No choice of a canonical increasing enumeration is needed. -/
theorem finiteLabelledCopyFibre_card_eq_aut
    {A K : Ordered3Graph Nat} {n : Nat}
    {v : Fin n → Nat}
    (hv : IsFiniteLabelledCopy A K n v) :
    @Fintype.card (FiniteLabelledCopyFibre A K n v)
      (finiteLabelledCopyFibre_fintype hv) =
    Fintype.card (FiniteHypergraphAut A n) := by
  classical
  letI : Fintype (FiniteLabelledCopyFibre A K n v) :=
    finiteLabelledCopyFibre_fintype hv
  exact Fintype.card_congr
    (finiteLabelledCopyFibre_equiv_aut hv).symm

end Ordered3Graph
end ThreeUniformDiaries
