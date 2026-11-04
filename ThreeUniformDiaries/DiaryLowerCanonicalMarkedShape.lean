import ThreeUniformDiaries.DiaryLowerColourSurjectivityBridge
import ThreeUniformDiaries.DiaryUpperBoundMarkedLeafAuxCode
import ThreeUniformDiaries.DiaryUpperBoundMarkedLeafExhaustion
import ThreeUniformDiaries.DiaryUpperBoundFiniteUnorderedCopyTransfer
import ThreeUniformDiaries.DiaryUpperBoundUnorderedCopyModelTransfer
import ThreeUniformDiaries.DiaryUpperBoundFiniteFrameZeroExtension
import ThreeUniformDiaries.DiaryFiniteLeafMeetCompleteReduct

/-!
# Track C lower: every actual labelled leaf copy yields a genuine marked diary

This is the TOTALITY half of the canonical lower colouring. The input is
an arbitrary finite labelled induced A-copy in a genuine countable RoleDiary;
the input need not be increasing in the diary's enumeration.

The sorted finite leaf-meet support is a full finite diary. We put all
labels at their actual indices in that support, and prove that the resulting
finite marked code belongs to the already deduplicated genuine family.
The ambient copy is pulled back along the actual finite auxiliary code;
no blanket assertion about arbitrary compressed-meet preservation is made.

This does NOT establish uniqueness of the marked code under the chosen
support representation, unavoidability inside every self-copy, or the final
big Ramsey lower bound. Those remain distinct Track C obligations.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- Package a bounded genuine diary and an actual finite aux code
into the exact marked-source family, with the source picture, full
length and each marked numerical position recorded literally.
No genericity of the target K is used. -/
theorem exists_genuineMarkedSource_of_finiteAuxCode
    {K : Ordered3Graph Nat}
    {a : Nat} (A : EnumNode a)
    (H : Ordered3Graph Nat) (m : Nat)
    (D : FiniteRoleDiaryBlock H m)
    (e : FiniteAuxEmbeddingImage
      (H.initialSegment m).toOrdered3Graph K m)
    (marked : Fin a → Fin m)
    (hLeaf : ∀ i : Fin a, IsLeaf H (marked i).val)
    (hCover : ∀ u : Nat, 3 ≤ u → u < m →
      IsLeaf H u → ∃ i : Fin a, (marked i).val = u)
    (hCopy : IsFiniteLabelledCopy A.toOrdered3Graph K a
      (fun i => e.image (marked i))) :
    ∃ T : MarkedFiniteSource 0 a,
      T ∈ allGenuineMarkedDiaryFinset A ∧
      T.source.k + 1 = m ∧
      T.source.picture.toOrdered3Graph = H ∧
      (∀ i : Fin a, (T.marked i).val = (marked i).val) := by
  classical
  cases m with
  | zero =>
      have hThree : 3 ≤ 0 := D.prediary.frame.length_ge_three
      omega
  | succ k =>
      let T : MarkedFiniteSource 0 a := {
        source := {
          k := k
          picture := H.initialSegment (k + 1)
          cut_le := by omega
        }
        marked := marked
      }
      have hFrameEq :
          (H.initialSegment (k + 1)).toOrdered3Graph = H :=
        D.zeroExtended_source_eq
      have hDiaryT :
          FiniteRoleDiaryBlock
            T.source.picture.toOrdered3Graph (T.source.k + 1) := by
        change FiniteRoleDiaryBlock
          (H.initialSegment (k + 1)).toOrdered3Graph (k + 1)
        rw [hFrameEq]
        exact D
      have hMarkedLeaf :
          ∀ i : Fin a,
            IsLeaf T.source.picture.toOrdered3Graph (T.marked i).val := by
        intro i
        change IsLeaf (H.initialSegment (k + 1)).toOrdered3Graph
          (marked i).val
        rw [hFrameEq]
        exact hLeaf i
      have hCovered :
          ∀ u : Nat, 3 ≤ u → u < T.source.k + 1 →
            IsLeaf T.source.picture.toOrdered3Graph u →
              ∃ i : Fin a, (T.marked i).val = u := by
        intro u hu3 hu h
        apply hCover u hu3 hu
        simpa only [T, hFrameEq] using h
      have hMarkedCopy :
          IsFiniteLabelledCopy A.toOrdered3Graph
            T.source.picture.toOrdered3Graph a
            (fun i => (T.marked i).val) := by
        change IsFiniteLabelledCopy A.toOrdered3Graph
          (H.initialSegment (k + 1)).toOrdered3Graph a
          (fun i => (marked i).val)
        exact e.pullback_labelledCopy
          A.toOrdered3Graph a marked hCopy
      have hShape : IsGenuineMarkedDiaryShape A T :=
        ⟨hDiaryT, hMarkedCopy, hMarkedLeaf, hCovered⟩
      refine ⟨T,
        (mem_allGenuineMarkedDiaryFinset_iff A T).mpr hShape,
        rfl, hFrameEq, ?_⟩
      intro i
      rfl

/-- Every ACTUAL induced labelled A-copy on genuine leaves produces
a full finite genuine marked diary. The choice of source is explicitly
constrained by the entire sorted support graph, its cardinality, and
the exact numeric rank of EACH prescribed labelled vertex.

This is a proved existence/classification result, not an assumed
factorisation hypothesis and not yet the lower-colouring persistence
theorem. -/
theorem exists_genuineMarkedDiary_of_labelledLeafCopy
    {K : Ordered3Graph Nat} (D : RoleDiary K)
    {a : Nat} (A : EnumNode a)
    (v : Fin a → Nat)
    (hLeaf : ∀ i : Fin a, IsLeaf K (v i))
    (hCopy : IsInducedLabelledCopy A K v) :
    ∃ T : MarkedFiniteSource 0 a,
      T ∈ allGenuineMarkedDiaryFinset A ∧
      T.source.k + 1 =
        (finiteLeafMeetSupport K
          ((Finset.univ : Finset (Fin a)).image v)).card ∧
      T.source.picture.toOrdered3Graph =
        finiteSupportGraph K
          (finiteLeafMeetSupport K
            ((Finset.univ : Finset (Fin a)).image v)) ∧
      (∀ i : Fin a,
        finiteSupportIndex
          (finiteLeafMeetSupport K
            ((Finset.univ : Finset (Fin a)).image v))
          (T.marked i).val = v i) := by
  classical
  obtain ⟨L, hL, hLeaves, e, marked, hMarkedImages,
      hMarkedLeaves, hExactIndices⟩ :=
    finiteLeafTuple_has_marked_actualAuxCode D a v hLeaf
  let S : Finset Nat := finiteLeafMeetSupport K L
  let H : Ordered3Graph Nat := finiteSupportGraph K S
  have hDiary : FiniteRoleDiaryBlock H S.card :=
    finiteLeafMeetSupport_is_finiteDiary D hLeaves
  have hMark : ∀ i : Fin a,
      finiteSupportIndex S (marked i).val = v i := by
    intro i
    calc
      finiteSupportIndex S (marked i).val =
          e.image (marked i) := (hExactIndices (marked i)).symm
      _ = v i := (hMarkedImages i).symm
  have hCovered :
      ∀ u : Nat, 3 ≤ u → u < S.card →
        IsLeaf H u → ∃ i : Fin a, (marked i).val = u :=
    finiteLeafMeetSupport_marking_covers_all_leaves
      D hLeaves v hL marked hMark
  have hCopyK : IsFiniteLabelledCopy A.toOrdered3Graph K a
      (fun i => e.image (marked i)) := by
    have hc : IsFiniteLabelledCopy A.toOrdered3Graph K a v :=
      (isInducedLabelledCopy_iff_fullUnordered A K v).mp hCopy
    have heq :
        (fun i : Fin a => e.image (marked i)) = v := by
      funext i
      exact (hMarkedImages i).symm
    simpa only [heq] using hc
  obtain ⟨T, hMem, hSize, hPicture, hMarks⟩ :=
    exists_genuineMarkedSource_of_finiteAuxCode
      A H S.card hDiary e marked hMarkedLeaves hCovered hCopyK
  refine ⟨T, hMem, ?_, ?_, ?_⟩
  · simpa only [S, hL] using hSize
  · simpa only [H, S, hL] using hPicture
  · intro i
    have hm :
        finiteSupportIndex S (T.marked i).val =
          finiteSupportIndex S (marked i).val := by
      rw [hMarks i]
    have hi := hm.trans (hMark i)
    simpa only [S, hL] using hi

end ATRFiniteDecoder
end ThreeUniformDiaries
