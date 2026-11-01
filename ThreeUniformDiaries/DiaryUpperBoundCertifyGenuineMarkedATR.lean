import ThreeUniformDiaries.DiaryUpperBoundGenuineMarkedFamily
import ThreeUniformDiaries.DiaryUpperBoundUniformGenuineMarkedBound
import ThreeUniformDiaries.DiaryUpperBoundFiniteUnorderedCopyTransfer

/-!
# Track A: certify a genuine marked diary source from its actual finite ATR code

For the sharp upper bound it is insufficient that the finite ATR
code happens to be based on a full diary: its prescribed marks must
be an induced labelled A-copy, and those marks must exhaust ALL
genuine leaves of the source.

The inducedness of the marking is NOT an additional assumption:
it follows by pulling back the ambient labelled A-copy through
the genuine finite ATR code (and its six-order unordered-edge
reflection). Only the diagram's full V/E/S axioms, genuine leaf
roles, and exact leaf coverage are separately required.

This is a reusable local certification lemma. The subsequent
leaf-generated support application will supply these hypotheses
from the canonical support extraction and its marked tuple.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- An actual finite ATR code with a full diary source, genuine
marked leaf roles and exhaustive leaf coverage represents a
genuine marked diary shape of A as soon as its marked image is
a labelled induced A-copy in the target generic hypergraph. -/
theorem genuineMarkedDiaryShape_of_actualATRCode
    (G : GenericEnumerated3Graph)
    {a : Nat} (A : EnumNode a)
    (S : MarkedFiniteSource 0 a)
    (e : S.source.Code G)
    (hDiary : FiniteRoleDiaryBlock
      S.source.picture.toOrdered3Graph (S.source.k + 1))
    (hLeaf : ∀ i : Fin a,
      IsLeaf S.source.picture.toOrdered3Graph (S.marked i).val)
    (hCover : ∀ u : Nat,
      3 ≤ u → u < S.source.k + 1 →
      IsLeaf S.source.picture.toOrdered3Graph u →
      ∃ i : Fin a, (S.marked i).val = u)
    (hCopy : IsFiniteLabelledCopy
      A.toOrdered3Graph G.graph a
      (fun i => e.image (S.marked i))) :
    IsGenuineMarkedDiaryShape A S := by
  refine ⟨hDiary, ?_, hLeaf, hCover⟩
  exact e.pullback_labelledCopy
    A.toOrdered3Graph a S.marked hCopy

/-- In particular the same actual ATR source is a member of
the complete, cutoff-free finite family of genuine marked diary
types. The size bound is derived from V/E/S rather than supplied
as an arbitrary numerical hypothesis. -/
theorem actualATRCode_mem_allGenuineMarkedDiaryShapes
    (G : GenericEnumerated3Graph)
    {a : Nat} (A : EnumNode a)
    (S : MarkedFiniteSource 0 a)
    (e : S.source.Code G)
    (hDiary : FiniteRoleDiaryBlock
      S.source.picture.toOrdered3Graph (S.source.k + 1))
    (hLeaf : ∀ i : Fin a,
      IsLeaf S.source.picture.toOrdered3Graph (S.marked i).val)
    (hCover : ∀ u : Nat,
      3 ≤ u → u < S.source.k + 1 →
      IsLeaf S.source.picture.toOrdered3Graph u →
      ∃ i : Fin a, (S.marked i).val = u)
    (hCopy : IsFiniteLabelledCopy
      A.toOrdered3Graph G.graph a
      (fun i => e.image (S.marked i))) :
    S ∈ allGenuineMarkedDiaryShapes A := by
  apply (mem_allGenuineMarkedDiaryShapes_iff A S).mpr
  exact genuineMarkedDiaryShape_of_actualATRCode
    G A S e hDiary hLeaf hCover hCopy

end ATRFiniteDecoder
end ThreeUniformDiaries
