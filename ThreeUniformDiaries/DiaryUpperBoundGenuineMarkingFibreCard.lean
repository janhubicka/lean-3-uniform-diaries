import ThreeUniformDiaries.DiaryGenuineMarkingFibreCardinality

/-!
# Track B compatibility API for genuine finite-diary marking fibres

The concrete automorphism torsor, its actual marking-fibre Fintype,
and the exact |Aut(A)| cardinality were already proven in
`DiaryGenuineMarkingFibreCardinality` (verified Track C PR #1015).

This file retains the established Track B names as thin wrappers
rather than maintaining a second copy of the complete
injectivity/surjectivity and preservation-of-roles argument.

The full finite diary source is unchanged by relabelling.
No countable lower bound, diary Ramsey theorem, or upper-bound
source-code factorisation is used.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- Compatibility name for the same true full-leaf marking fibre
used by the verified Track C automorphism calculation. -/
abbrev GenuineMarkingsOfDiary
    {a : Nat} (A : EnumNode a)
    (S : ProtectedSource 0) : Type :=
  GenuineDiaryMarkingFibre A S

/-- The existing Track B equivalence is the exact same verified
automorphism torsor, with the chosen marking as basepoint. -/
noncomputable def genuineMarkingsOfDiary_equiv_aut
    {a : Nat} (A : EnumNode a)
    (S : ProtectedSource 0)
    (p : Fin a → Fin (S.k + 1))
    (hp : IsGenuineMarkedDiaryShape A ⟨S, p⟩) :
    FiniteHypergraphAut A.toOrdered3Graph a ≃
      GenuineMarkingsOfDiary A S :=
  genuineDiaryMarkingFibre_equiv_aut A S ⟨p, hp⟩

/-- Preserve the previously exported Fintype interface, now
obtained from one canonical construction. -/
noncomputable def genuineMarkingsOfDiaryFintype
    {a : Nat} (A : EnumNode a)
    (S : ProtectedSource 0)
    (p : Fin a → Fin (S.k + 1))
    (hp : IsGenuineMarkedDiaryShape A ⟨S, p⟩) :
    Fintype (GenuineMarkingsOfDiary A S) :=
  genuineDiaryMarkingFibre_fintype A S ⟨p, hp⟩

/-- Exact count of full-leaf genuine markings, reusing the
single verified Track C theorem without an independent proof. -/
theorem genuineMarkingsOfDiary_card_eq_aut
    {a : Nat} (A : EnumNode a)
    (S : ProtectedSource 0)
    (p : Fin a → Fin (S.k + 1))
    (hp : IsGenuineMarkedDiaryShape A ⟨S, p⟩) :
    @Fintype.card (GenuineMarkingsOfDiary A S)
      (genuineMarkingsOfDiaryFintype A S p hp) =
        Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) :=
  genuineDiaryMarkingFibre_card_eq_aut A S ⟨p, hp⟩

end ATRFiniteDecoder
end ThreeUniformDiaries
