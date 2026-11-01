import ThreeUniformDiaries.DiaryUpperBoundFiniteMarkedUniverse
import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface
import ThreeUniformDiaries.DiaryFiniteAutTorsor

/-!
# Track A: the finite family of genuinely marked full diary types

The coarse marked ATR universe contains ALL finite enumerated
3-hypergraphs and all markings. For the sharp degree upper bound,
only genuine finite FULL diaries with a prescribed labelled copy
of A occupying precisely their genuine leaves are relevant.

This file extracts that exact finite family *without* assuming
that an arbitrary A-copy already has a suitable ATR code. Those
geometric existence and factorisation statements are separate,
currently in the Track A finite-support PR stack.

- The source finite frame satisfies literal V/E/S diary axioms.
- The distinguished tuple is an induced labelled copy of A,
  not necessarily in increasing target order.
- Every marked coordinate is a genuine leaf.
- Every genuine bounded leaf is among the marked coordinates.
- A finite size bound is imposed externally; the uniform bound
  from DiaryFiniteSupportCardinality can later supply it.

The bounded list is deduplicated by converting through Finset.
It therefore counts finite marked source diagrams, rather than
raw repeated enumeration instances.

The agreement between its cardinality and the manuscript's
"number of diaries times |Aut(A)|" remains a separate counting
theorem; no false equality is inserted here.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- A finite marked ATR source which is *actually* a full diary
and whose complete genuine leaf set consists of the marked,
labelled induced copy of A. A single shape may have several
different valid markings. -/
def IsGenuineMarkedDiaryShape {a : Nat}
    (A : EnumNode a) (S : MarkedFiniteSource 0 a) : Prop :=
  let H := S.source.picture.toOrdered3Graph
  let m := S.source.k + 1
  FiniteRoleDiaryBlock H m ∧
  IsFiniteLabelledCopy A.toOrdered3Graph H a
    (fun i => (S.marked i).val) ∧
  (∀ i : Fin a, IsLeaf H (S.marked i).val) ∧
  (∀ u : Nat, 3 ≤ u → u < m → IsLeaf H u →
    ∃ i : Fin a, (S.marked i).val = u)

/-- The *deduplicated* finite family of all genuine marked full
diaries representing labelled A, with source size at most M. -/
noncomputable def genuineMarkedDiaryFamily
    {a : Nat} (A : EnumNode a) (M : Nat) :
    List (MarkedFiniteSource 0 a) := by
  classical
  exact (((boundedMarkedATRUniverse a M).toFinset).filter
    (fun S => IsGenuineMarkedDiaryShape A S)).toList

/-- Complete characterisation of family membership: no genuine
bounded marked diary source is lost, and no non-diary source or
spurious marking is retained. -/
theorem mem_genuineMarkedDiaryFamily
    {a : Nat} (A : EnumNode a) (M : Nat)
    (S : MarkedFiniteSource 0 a) :
    S ∈ genuineMarkedDiaryFamily A M ↔
      S.source.k + 1 ≤ M ∧
      IsGenuineMarkedDiaryShape A S := by
  classical
  change S ∈ (((boundedMarkedATRUniverse a M).toFinset).filter
    (fun X => IsGenuineMarkedDiaryShape A X)).toList ↔
      S.source.k + 1 ≤ M ∧ IsGenuineMarkedDiaryShape A S
  constructor
  · intro h
    have h' : S ∈ ((boundedMarkedATRUniverse a M).toFinset).filter
        (fun X => IsGenuineMarkedDiaryShape A X) :=
      (Finset.mem_toList).mp h
    rcases Finset.mem_filter.mp h' with ⟨hUniv, hShape⟩
    have hSource : S ∈ boundedMarkedATRUniverse a M := by
      simpa using hUniv
    exact ⟨boundedATRUniverse_mem_size a M S hSource, hShape⟩
  · rintro ⟨hBound, hShape⟩
    apply Finset.mem_toList.mpr
    apply Finset.mem_filter.mpr
    refine ⟨?_, hShape⟩
    simpa using (markedSource_mem_boundedATRUniverse S hBound)

/-- Membership certifies the bounded full finite diary axioms,
the actual labelled induced A-copy, and equality of the
bounded source leaf set with the distinguished labels. -/
theorem genuineMarkedDiaryFamily_sound
    {a : Nat} (A : EnumNode a) (M : Nat)
    (S : MarkedFiniteSource 0 a)
    (hS : S ∈ genuineMarkedDiaryFamily A M) :
    IsGenuineMarkedDiaryShape A S :=
  ((mem_genuineMarkedDiaryFamily A M S).mp hS).2

/-- This is the precise finite candidate count. It is a
mathematically defined sharp-family parameter, not yet identified
with any other published diary-count notation. -/
def genuineMarkedDiaryCount {a : Nat}
    (A : EnumNode a) (M : Nat) : Nat :=
  (genuineMarkedDiaryFamily A M).length

/-- A common finite ATR refinement uses at most the number of
genuine bounded marked diary types, PROVIDED the chosen A-copies
factor through these genuine codes. The missing geometric
factorisation hypothesis is explicit; no diary Ramsey theorem
or countable unavoidability is involved. -/
theorem actualFiniteAuxRamsey_genuineMarkedDiaryPalette
    (G : GenericEnumerated3Graph) {a : Nat} (A : EnumNode a)
    (M : Nat) (ψ : Nat → Nat)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : (Fin a → Nat) → κ) :
    ∃ (u : Embedding G.graph G.graph) (hu : u.AuxTypeRespecting),
      ∃ palette : List κ,
        palette.length = genuineMarkedDiaryCount A M ∧
        ∀ v : Fin a → Nat,
          (∃ S ∈ genuineMarkedDiaryFamily A M,
            ∃ e : S.source.Code G,
              ∀ i, v i = e.image (S.marked i)) →
          χ (fun i => ψ (u (v i))) ∈ palette := by
  simpa only [genuineMarkedDiaryCount] using
    actualFiniteAuxRamsey_markedPalette_zero G a ψ χ
      (genuineMarkedDiaryFamily A M)

end ATRFiniteDecoder
end ThreeUniformDiaries
