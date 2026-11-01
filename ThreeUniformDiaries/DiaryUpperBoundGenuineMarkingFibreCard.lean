import ThreeUniformDiaries.DiaryUpperBoundMarkedAutFibre

/-!
# Track B: exact genuine markings count for a fixed finite diary

For a fixed complete finite diary whose leaves form one labelled
copy of A, every other genuine exhaustive marking is obtained by
precomposing the chosen marking with a unique source automorphism.

We turn the already verified source-level uniqueness theorem into
a genuine equivalence of finite types and an exact cardinality
calculation. This is the precise per-diary factor |Aut(A)|.

The final global sum over all different unmarked diary shapes is
a separate obligation; neither Ramsey nor unavoidability enters.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- The genuine exhaustive leaf markings of one fixed unmarked
source diary. -/
def GenuineMarkingsOfDiary
    {a : Nat} (A : EnumNode a)
    (S : ProtectedSource 0) : Type :=
  { q : Fin a → Fin (S.k + 1) //
      IsGenuineMarkedDiaryShape A ⟨S, q⟩ }

/-- Every valid marking of the same diary is a unique
Aut(A)-relabel of a chosen marking. -/
noncomputable def genuineMarkingsOfDiary_equiv_aut
    {a : Nat} (A : EnumNode a)
    (S : ProtectedSource 0)
    (p : Fin a → Fin (S.k + 1))
    (hp : IsGenuineMarkedDiaryShape A ⟨S, p⟩) :
    FiniteHypergraphAut A.toOrdered3Graph a ≃
      GenuineMarkingsOfDiary A S := by
  classical
  have hpCopy : IsFiniteLabelledCopy
      A.toOrdered3Graph S.picture.toOrdered3Graph a
      (fun i => (p i).val) := by
    dsimp [IsGenuineMarkedDiaryShape] at hp
    exact hp.2.1
  have hForward (σ : FiniteHypergraphAut A.toOrdered3Graph a) :
      IsGenuineMarkedDiaryShape A ⟨S, fun i => p (σ.val i)⟩ := by
    dsimp [IsGenuineMarkedDiaryShape] at hp ⊢
    rcases hp with ⟨hDiary,hCopy,hLeaf,hCover⟩
    refine ⟨hDiary, finiteLabelledCopy_relabel hCopy σ, ?_, ?_⟩
    · intro i
      exact hLeaf (σ.val i)
    · intro u hu3 hum huLeaf
      obtain ⟨j,hj⟩ := hCover u hu3 hum huLeaf
      refine ⟨σ.val.symm j, ?_⟩
      simpa only [Equiv.apply_symm_apply] using hj
  let forward : FiniteHypergraphAut A.toOrdered3Graph a →
      GenuineMarkingsOfDiary A S :=
    fun σ => ⟨fun i => p (σ.val i), hForward σ⟩
  have hinj : Function.Injective forward := by
    intro σ τ h
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply hpCopy.1
    exact congrArg
      (fun q : GenuineMarkingsOfDiary A S => (q.val i).val) h
  have hsurj : Function.Surjective forward := by
    intro q
    obtain ⟨σ,hσ,_⟩ :=
      genuineMarkedDiaryShape_unique_aut_between_markings
        A S p q.val hp q.property
    refine ⟨σ, ?_⟩
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact (hσ i).symm
  exact Equiv.ofBijective forward ⟨hinj,hsurj⟩

/-- Finiteness of the genuine marking fibre is transported from
the finite actual automorphism group. -/
noncomputable def genuineMarkingsOfDiaryFintype
    {a : Nat} (A : EnumNode a)
    (S : ProtectedSource 0)
    (p : Fin a → Fin (S.k + 1))
    (hp : IsGenuineMarkedDiaryShape A ⟨S, p⟩) :
    Fintype (GenuineMarkingsOfDiary A S) :=
  Fintype.ofEquiv (FiniteHypergraphAut A.toOrdered3Graph a)
    (genuineMarkingsOfDiary_equiv_aut A S p hp)

/-- Exact cardinality of all valid markings of one genuine diary:
the number is precisely the size of the actual source Aut(A). -/
theorem genuineMarkingsOfDiary_card_eq_aut
    {a : Nat} (A : EnumNode a)
    (S : ProtectedSource 0)
    (p : Fin a → Fin (S.k + 1))
    (hp : IsGenuineMarkedDiaryShape A ⟨S, p⟩) :
    @Fintype.card (GenuineMarkingsOfDiary A S)
      (genuineMarkingsOfDiaryFintype A S p hp) =
        Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) := by
  classical
  letI : Fintype (GenuineMarkingsOfDiary A S) :=
    genuineMarkingsOfDiaryFintype A S p hp
  exact Fintype.card_congr
    (genuineMarkingsOfDiary_equiv_aut A S p hp).symm

end ATRFiniteDecoder
end ThreeUniformDiaries
