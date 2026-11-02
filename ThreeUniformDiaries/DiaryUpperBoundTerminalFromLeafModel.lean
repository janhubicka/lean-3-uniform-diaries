import ThreeUniformDiaries.DiaryUpperBoundGenuineLeafFactorisation
import ThreeUniformDiaries.DiarySharpConditionalUpperCount

/-!
# Track A: direct sharp upper bound from a diary leaf model

The geometric finite marked source-code factorisation has been
isolated and formalised in the preceding module. The exact
marked/unmarked finite family count, with ONE factor |Aut(A)|,
is also verified independently.

This file composes them with the already verified **unordered**
ambient direct-transfer theorem. The ambient copy is an actual
unordered induced self-embedding of U; no auxiliary preservation
of U's own numerical ordering is assumed.

The indispensable structural input is a countable full diary D
and an induced embedding of the original U into the leaves of D.
We do not silently identify U with the diary's whole vertex set.

For modularity the last hypothesis `hCopyTransport` asserts that
labelled copies of A remain induced after the prescribed unordered
map into diary leaves and the chosen aux-type-respecting map into
generic G. This is a purely relational consequence of unordered
inducedness (to be discharged by the separate labelled-copy
predicate compatibility and transport lemma). It is not a
finite ATR factorisation hypothesis and does not contain
the desired Ramsey conclusion.

No countable unavoidability, flip absorption, or circular
invocation of the final diary Ramsey theorem occurs.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- Given a genuine countable diary leaf model and actual maps
into and out of enumerated generic G, every labelled A-copy in
the ambient unordered U has at most the sharp finite genuine
diary count times Aut(A) colours in one induced self-copy.

The geometric finite code COVER is proved rather than assumed:
only the elementary labelled-copy transport through the
prescribed graph embeddings remains an explicit parameter.
The count concerns all distinct unmarked finite diary
presentations in the canonical cutoff-free source family. -/
theorem actualFiniteAuxRamsey_upper_of_diaryLeafModel_and_copyTransport
    (G : GenericEnumerated3Graph)
    (U H : Ordered3Graph Nat)
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H)
    (hLeafRange : ∀ x : Nat, IsLeaf H (F x))
    (η : Embedding H G.graph)
    (hη : η.AuxTypeRespecting)
    (ψ : UnorderedEmbedding G.graph U)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : (Fin a → Nat) → κ)
    (hCopyTransport :
      ∀ v : Fin a → Nat,
        IsInducedLabelledCopy A U v →
        IsFiniteLabelledCopy
          A.toOrdered3Graph G.graph a
          (fun i => η (F (v i)))) :
    ∃ w : UnorderedEmbedding U U,
      ∃ palette : List κ,
        palette.length =
          (allGenuineUnmarkedDiarySources A).card *
          Fintype.card
            (FiniteHypergraphAut A.toOrdered3Graph a) ∧
        ∀ v : Fin a → Nat,
          IsInducedLabelledCopy A U v →
          χ (fun i => w (v i)) ∈ palette := by
  let phi : UnorderedEmbedding U G.graph :=
    (η.asUnordered).comp F
  have hFactors :
      ∀ v : Fin a → Nat,
        IsInducedLabelledCopy A U v →
        ∃ S ∈ allGenuineMarkedDiaryShapes A,
          ∃ c : S.source.Code G,
            ∀ i : Fin a, phi (v i) = c.image (S.marked i) := by
    intro v hv
    have hLeaves :
        ∀ i : Fin a, IsLeaf H (F (v i)) := by
      intro i
      exact hLeafRange (v i)
    obtain ⟨S,hS,c,hCodes⟩ :=
      finiteDiaryLeafTuple_genuineMarkedGenericFactorisation
        G H D η hη A (fun i => F (v i))
        hLeaves (hCopyTransport v hv)
    refine ⟨S,hS,c,?_⟩
    intro i
    change η (F (v i)) = c.image (S.marked i)
    exact hCodes i
  exact actualFiniteAuxRamsey_direct_upper_genuineDiaryCount
    G U A phi ψ χ hFactors

end ATRFiniteDecoder
end ThreeUniformDiaries
