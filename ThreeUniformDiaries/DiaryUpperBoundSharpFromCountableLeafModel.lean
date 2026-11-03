import ThreeUniformDiaries.DiaryUpperBoundTerminalFromLeafModel
import ThreeUniformDiaries.DiaryUpperBoundUnorderedCopyModelTransfer
import ThreeUniformDiaries.DiaryUpperBoundActualCodeToGeneric

/-!
# Track A: sharp upper bound from a countable diary leaf model

This is the fully assembled noncircular big-Ramsey UPPER bound
in its correct structural form.

Suppose the countably universal unordered 3-hypergraph U admits
an induced unordered embedding F into the genuine leaves of some
countable full diary H. Then the verified K_I universal embedding
places H aux-type-respectingly into the enumerated generic G, and
universality places an unordered induced copy of G back into U.

The literal finite leaf-meet support of each labelled A-copy
gives an actual finite aux code of a genuine full diary with
exactly that prescribed marked A-copy (Track A geometric source
factorisation). A single finite ATR Ramsey refinement then
homogenises one colour per genuine marked diary shape.

The count of these shapes has already been verified as the
number of distinct genuine UNMARKED finite diary sources of A
times the actual source automorphism cardinal |Aut(A)|. This
factor is applied exactly once.

Crucially, the labelled-copy transport through F and the
global generic aux embedding is proved from relational
inducedness. There is NO auxiliary code-cover premise, NO
unproved type-respecting to aux-type-respecting implication,
NO ordered assumption on F, NO countable unavoidability,
and NO invocation of the final diary Ramsey theorem.

The *only* open structural issue for the universal case is
the existence of a suitable countable full diary leaf model
for arbitrary U; this is distinct from countable unavoidability,
and is isolated by Track B's shifted-seed/V3 construction.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- Full sharp upper bound for every countably universal U that
has an induced copy inside the genuine leaves of a countable
full diary. The unordered induced target self-copy is an
actual morphism, and its colour palette has cardinality at
most the number of unmarked full diary shapes times |Aut(A)|.

NO finite source-code factorisation, labelled-copy transport,
or generic-to-U embedding is postulated; all are constructed
from the indicated full diary leaf model and the universality
hypothesis. No countable lower-bound unavoidability is used. -/
theorem actualFiniteAuxRamsey_sharp_upper_of_diaryLeafModel
    (G : GenericEnumerated3Graph)
    (U H : Ordered3Graph Nat)
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H)
    (hLeafRange : ∀ x : Nat, IsLeaf H (F x))
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : (Fin a → Nat) → κ) :
    ∃ w : UnorderedEmbedding U U,
      ∃ palette : List κ,
        palette.length =
          (allGenuineUnmarkedDiarySources A).card *
          Fintype.card
            (FiniteHypergraphAut A.toOrdered3Graph a) ∧
        ∀ v : Fin a → Nat,
          IsInducedLabelledCopy A U v →
          χ (fun i => w (v i)) ∈ palette := by
  classical
  obtain ⟨η,hη,_,_⟩ :=
    exists_auxTypeRespecting_embedding_fix_two G H
  let ψ : UnorderedEmbedding G.graph U :=
    Classical.choice (hUniversal G.graph)
  apply actualFiniteAuxRamsey_upper_of_diaryLeafModel_and_copyTransport
    G U H D F hLeafRange η hη ψ A χ
  intro v hv
  exact finiteLabelledCopy_after_diaryLeafAndGeneric
    G U H A F η v hv

end ATRFiniteDecoder
end ThreeUniformDiaries
