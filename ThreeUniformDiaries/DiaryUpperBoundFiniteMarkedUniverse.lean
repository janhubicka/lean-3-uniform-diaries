import ThreeUniformDiaries.DiaryUpperBoundMarkedFiniteColours
import ThreeUniformDiaries.DiaryFiniteATRShapeUniverse

/-!
# Track A: finite universe of bounded marked actual ATR sources

Every marked diary A-copy is represented by an ACTUAL finite ATR
source (not a zero-extended infinite embedding), together with a
position for each labelled vertex of A.

For a fixed number a of marked coordinates and a fixed positive
upper bound M on the source size, there are only finitely many
such source codes:
- source sizes k+1 <= M (k : Fin M);
- finitely many EnumNode (k+1) hypergraphs;
- finitely many maps Fin a -> Fin (k+1).

The list constructed here contains ALL such bounded marked source
data, including repeated source shapes with different markings.
It is only an upper universe: it does not identify the exactly
realisable marked FULL diary shapes or prove the sharp diary count.

Combined with a uniform support cardinality bound (Track C #991)
and the actual marked finite source code (Track A #1000), it
will yield a completely independent finite big-Ramsey upper bound
without countable diary unavoidability. The sharp count requires
the smaller genuine-diary subfamily and the Aut(A) accounting.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

/-- Concrete finite coding space for arbitrary marked sources
with positive size at most M. The finite datum is the source
k, its ACTUAL (k+1)-vertex hypergraph and the marked positions. -/
abbrev BoundedMarkedATRCode (a M : Nat) : Type :=
  Σ k : Fin M, EnumNode (k.val + 1) ×
    (Fin a → Fin (k.val + 1))

noncomputable instance boundedMarkedATRCodeFintype (a M : Nat) :
    Fintype (BoundedMarkedATRCode a M) := by
  classical
  infer_instance

/-- Forget the finite-size certificate to obtain the actual
marked protected ATR source at cut zero. -/
def BoundedMarkedATRCode.toMarkedSource
    {a M : Nat} (C : BoundedMarkedATRCode a M) :
    MarkedFiniteSource 0 a where
  source := {
    k := C.1.val
    picture := C.2.1
    cut_le := by omega
  }
  marked := C.2.2

/-- An explicit FINITE list of ALL possible marked actual
ATR source shapes with at most M genuine vertices. -/
noncomputable def boundedMarkedATRUniverse (a M : Nat) :
    List (MarkedFiniteSource 0 a) := by
  classical
  exact
    ((Finset.univ : Finset (BoundedMarkedATRCode a M)).toList).map
      (fun C => C.toMarkedSource)

/-- Every actual marked source whose cardinality is bounded by M
appears in the literal finite universe. No diary or genericity
assumption is imposed. This includes source repetitions and
arbitrary labelled coordinate maps. -/
theorem markedSource_mem_boundedATRUniverse
    {a M : Nat} (S : MarkedFiniteSource 0 a)
    (hBound : S.source.k + 1 ≤ M) :
    S ∈ boundedMarkedATRUniverse a M := by
  classical
  let k : Fin M := ⟨S.source.k, by omega⟩
  let C : BoundedMarkedATRCode a M :=
    ⟨k, (S.source.picture, S.marked)⟩
  apply List.mem_map.mpr
  refine ⟨C, by simp [boundedMarkedATRUniverse], ?_⟩
  cases S with
  | mk source marked =>
    cases source with
    | mk size picture hCut =>
      rfl

/-- Each source listed in the universe has size at most M;
there is no accidental unbounded shape or fictitious source
tail in the list. -/
theorem boundedATRUniverse_mem_size
    (a M : Nat)
    (S : MarkedFiniteSource 0 a)
    (hMem : S ∈ boundedMarkedATRUniverse a M) :
    S.source.k + 1 ≤ M := by
  classical
  obtain ⟨C,_,hEq⟩ := List.mem_map.mp hMem
  rw [← hEq]
  change C.1.val + 1 ≤ M
  exact C.1.isLt

end ATRFiniteDecoder
end ThreeUniformDiaries
