import ThreeUniformDiaries.DiaryUpperBoundPackageMarkedSource
import ThreeUniformDiaries.DiaryUpperBoundMarkedLeafAuxCode
import ThreeUniformDiaries.DiaryUpperBoundMarkedLeafExhaustion
import ThreeUniformDiaries.DiaryUpperBoundActualCodeToGeneric

/-!
# Track A: the exact marked diary factorisation for arbitrary finite leaf tuples

This is the central geometric missing lemma of the sharp big-Ramsey
upper bound, **conditional only** on (a) a countable full diary
structure on the ordered target H, (b) a global aux-type-respecting
embedding of H into enumerated generic G, and (c) the fact that
the specified labelled leaf tuple genuinely induces A there.

There is no additional *factorisation hypothesis*.

Given the prescribed leaf tuple, use the verified full finite
leaf-meet support and its exact actual finite ATR inclusion;
mark the original leaves in that code, prove the marks exhaust
the whole source leaf set, and postcompose with the ambient
aux-type-respecting embedding into G. The finite frame
identification and unordered-copy pullback then package this
exact data as a member of the previously verified complete
finite family of genuine marked diary types.

The source labels are NOT required to be numerically increasing.
The source code has precisely its genuine finite vertices;
there are no extra tests on any zero-extended source tail.
This theorem uses neither diary Ramsey nor countable unavoidability.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- Every finite labelled A-copy on genuine leaves of a full
countable diary factors through an ACTUAL genuine marked finite
full diary ATR source code in the enumerated generic hypergraph.

The target tuple is the exact image of the originally prescribed
leaf tuple under the given global auxiliary embedding of the
whole diary: not some unspecified isomorphic copy.

The only `hCopy` hypothesis asserts that this prescribed tuple
already induces A; membership in the finite marked family and
auxiliary code admissibility are both PROVED conclusions. -/
theorem finiteDiaryLeafTuple_genuineMarkedGenericFactorisation
    (G : GenericEnumerated3Graph)
    (H : Ordered3Graph Nat)
    (D : RoleDiary H)
    (η : Embedding H G.graph)
    (hη : η.AuxTypeRespecting)
    {a : Nat} (A : EnumNode a)
    (v : Fin a → Nat)
    (hLeaf : ∀ i : Fin a, IsLeaf H (v i))
    (hCopy : IsFiniteLabelledCopy
      A.toOrdered3Graph G.graph a (fun i => η (v i))) :
    ∃ S : MarkedFiniteSource 0 a,
      S ∈ allGenuineMarkedDiaryShapes A ∧
      ∃ c : S.source.Code G,
        ∀ i : Fin a, η (v i) = c.image (S.marked i) := by
  classical
  obtain ⟨L,hL,hLeaves,e,marked,hMarkedImages,
      hMarkedLeaves,hExactIndices⟩ :=
    finiteLeafTuple_has_marked_actualAuxCode
      D a v hLeaf
  let supp : Finset Nat := finiteLeafMeetSupport H L
  let source : Ordered3Graph Nat := finiteSupportGraph H supp
  have hFiniteDiary :
      FiniteRoleDiaryBlock source supp.card :=
    finiteLeafMeetSupport_is_finiteDiary D hLeaves
  have hIndices :
      ∀ i : Fin a,
        finiteSupportIndex supp (marked i).val = v i := by
    intro i
    calc
      finiteSupportIndex supp (marked i).val =
          e.image (marked i) := (hExactIndices (marked i)).symm
      _ = v i := (hMarkedImages i).symm
  have hCovered :
      ∀ u : Nat, 3 ≤ u → u < supp.card →
        IsLeaf source u →
        ∃ i : Fin a, (marked i).val = u :=
    finiteLeafMeetSupport_marking_covers_all_leaves
      D hLeaves v hL marked hIndices
  let cGeneric :
      FiniteAuxEmbeddingImage
        (source.initialSegment supp.card).toOrdered3Graph
        G.graph supp.card :=
    e.postcompose η hη
  have hGenericImages :
      ∀ i : Fin a,
        cGeneric.image (marked i) = η (v i) := by
    intro i
    calc
      cGeneric.image (marked i) =
          η (e.image (marked i)) := by
        simp only [cGeneric,
          FiniteAuxEmbeddingImage.postcompose_apply]
      _ = η (v i) := congrArg η (hMarkedImages i).symm
  have hCopyCode :
      IsFiniteLabelledCopy
        A.toOrdered3Graph G.graph a
        (fun i => cGeneric.image (marked i)) := by
    have heq :
        (fun i : Fin a => cGeneric.image (marked i)) =
          (fun i : Fin a => η (v i)) := by
      funext i
      exact hGenericImages i
    rw [heq]
    exact hCopy
  obtain ⟨S,hShape,c,hMark⟩ :=
    exists_genuineMarkedSource_of_actualFiniteDiaryCode
      G A source supp.card hFiniteDiary
      cGeneric marked hMarkedLeaves hCovered hCopyCode
  refine ⟨S,hShape,c,?_⟩
  intro i
  calc
    η (v i) = cGeneric.image (marked i) :=
      (hGenericImages i).symm
    _ = c.image (S.marked i) := (hMark i).symm

end ATRFiniteDecoder
end ThreeUniformDiaries
