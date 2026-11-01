import ThreeUniformDiaries.DiaryUpperBoundMarkedAutFibre
import ThreeUniformDiaries.DiaryFiniteAutFibreCardinality

/-!
# Track C: exact cardinality of full-leaf markings on one finite diary

A genuine marked full diary is a bounded complete V/E/S diary with
a labelled induced A-copy whose image is EXACTLY its genuine leaves.

For a FIXED underlying finite source B, a nonempty family of
genuine markings is a principal homogeneous Aut(A)-set. This
makes the sharp multiplicity concrete: the fibre of the
forgetful map (B,marking) ↦ B has precisely |Aut(A)| elements.

This is not the global sharp degree formula. The remaining finite
step must sum these uniform fibres over the deduplicated unmarked
diary sources. The entirely separate diary ATR-code cover and
countable lower bound are also not assumed here.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- Markings of one fixed finite genuine diary source S which
represent a labelled induced copy of A occupying *all* the
true bounded leaves of S. -/
def GenuineDiaryMarkingFibre
    {a : Nat} (A : EnumNode a) (S : ProtectedSource 0) : Type :=
  { p : Fin a → Fin (S.k + 1) //
    IsGenuineMarkedDiaryShape A ⟨S, p⟩ }

/-- A genuine full-leaf marking can be relabelled by any actual
automorphism of A, without changing the source diary B. -/
noncomputable def genuineDiaryMarkingFibre_relabel
    {a : Nat} (A : EnumNode a) (S : ProtectedSource 0)
    (p₀ : GenuineDiaryMarkingFibre A S)
    (σ : FiniteHypergraphAut A.toOrdered3Graph a) :
    GenuineDiaryMarkingFibre A S := by
  let p : Fin a → Fin (S.k + 1) :=
    fun i => p₀.val (σ.val i)
  have hshape : IsGenuineMarkedDiaryShape A ⟨S, p₀.val⟩ :=
    p₀.property
  dsimp [IsGenuineMarkedDiaryShape] at hshape ⊢
  obtain ⟨hFull, hCopy, hLeaf, hCover⟩ := hshape
  refine ⟨p, hFull, ?_, ?_, ?_⟩
  · exact finiteLabelledCopy_relabel hCopy σ
  · intro i
    exact hLeaf (σ.val i)
  · intro u hu3 hum huLeaf
    obtain ⟨i, hi⟩ := hCover u hu3 hum huLeaf
    refine ⟨σ.val.symm i, ?_⟩
    simpa only [p, Equiv.apply_symm_apply] using hi

/-- The fibre over a fixed source B is EQUIVALENT to the true
finite automorphism group of A, once the fibre is nonempty.
The equivalence is based at one genuine marking, not at any
unproved canonical labelling of B. -/
noncomputable def genuineDiaryMarkingFibre_equiv_aut
    {a : Nat} (A : EnumNode a) (S : ProtectedSource 0)
    (p₀ : GenuineDiaryMarkingFibre A S) :
    FiniteHypergraphAut A.toOrdered3Graph a ≃
      GenuineDiaryMarkingFibre A S := by
  classical
  let f : FiniteHypergraphAut A.toOrdered3Graph a →
      GenuineDiaryMarkingFibre A S :=
    genuineDiaryMarkingFibre_relabel A S p₀
  have hcopy : Function.Injective
      (fun i : Fin a => (p₀.val i).val) := by
    have hp : IsGenuineMarkedDiaryShape A ⟨S, p₀.val⟩ :=
      p₀.property
    dsimp [IsGenuineMarkedDiaryShape] at hp
    exact hp.2.1.1
  have hinj : Function.Injective f := by
    intro σ τ heq
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply hcopy
    have hvalue := congrArg
      (fun q : GenuineDiaryMarkingFibre A S => (q.val i).val) heq
    exact hvalue
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨σ, hσ, _⟩ :=
      genuineMarkedDiaryShape_unique_aut_between_markings
        A S p₀.val q.val p₀.property q.property
    refine ⟨σ, ?_⟩
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact (hσ i).symm
  exact Equiv.ofBijective f ⟨hinj, hsurj⟩

/-- Nonempty genuine marking fibres are actually finite. -/
noncomputable def genuineDiaryMarkingFibre_fintype
    {a : Nat} (A : EnumNode a) (S : ProtectedSource 0)
    (p₀ : GenuineDiaryMarkingFibre A S) :
    Fintype (GenuineDiaryMarkingFibre A S) := by
  classical
  exact Fintype.ofEquiv
    (FiniteHypergraphAut A.toOrdered3Graph a)
    (genuineDiaryMarkingFibre_equiv_aut A S p₀)

/-- Exact individual fibre cardinality, on genuine finite
marked diary shapes rather than only abstract labelled copies. -/
theorem genuineDiaryMarkingFibre_card_eq_aut
    {a : Nat} (A : EnumNode a) (S : ProtectedSource 0)
    (p₀ : GenuineDiaryMarkingFibre A S) :
    @Fintype.card (GenuineDiaryMarkingFibre A S)
      (genuineDiaryMarkingFibre_fintype A S p₀) =
    Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) := by
  classical
  letI : Fintype (GenuineDiaryMarkingFibre A S) :=
    genuineDiaryMarkingFibre_fintype A S p₀
  exact Fintype.card_congr
    (genuineDiaryMarkingFibre_equiv_aut A S p₀).symm

end ATRFiniteDecoder
end ThreeUniformDiaries
