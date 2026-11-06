import ThreeUniformDiaries.DiaryLowerExactCountUnconditionalLeafModel
import ThreeUniformDiaries.DiaryConcreteCountablyUniversalWitness
import ThreeUniformDiaries.DiarySumOverAllIncreasingPresentations
import ThreeUniformDiaries.DiaryUnlabelledCopyDomainEquivalence

/-!
# Track C: every finite 3-hypergraph has a genuine full diary

The complete exact degree formula uses a finite, deduplicated family
of actual full V/E/S diaries, not arbitrary Boolean source pictures.
We independently verify this family is NEVER empty.

Use the explicit countably universal pair-coded 3-hypergraph, a real
finite labelled induced A-copy in it, and the already checked finite
canonical marked-diary colouring (the full lower theorem's geometric
construction). Its value supplies a REAL marked diary, whose
unmarked projection is a REAL full diary of the underlying A.

Consequently the sum of diary counts over all increasing ordered
presentations is strictly positive. This does not use the terminal
exact big Ramsey degree equality, a numerical lower bound, or any
countable-source diary unavoidability hypothesis.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open _root_.ThreeUniformDiaries.Ordered3Graph

/-- The complete finite family of real marked full diaries
of ANY finite 3-hypergraph A is inhabited. Its witness is
obtained geometrically from an ACTUAL finite induced A-copy,
not from the numerical big Ramsey degree theorem. -/
theorem allGenuineMarkedDiaryFinset_nonempty
    {a : Nat} (A : EnumNode a) :
    (allGenuineMarkedDiaryFinset A).Nonempty := by
  classical
  let U : Ordered3Graph Nat := canonicalGenericEnumerated3Graph.graph
  have hU : CountablyUniversal U :=
    canonicalGeneric_countablyUniversal
  obtain ⟨v⟩ :=
    nonempty_genuineFiniteEmbeddings_of_universal U hU A
  obtain ⟨χ, _hUnavoidable⟩ :=
    exists_unavoidableMarkedDiaryColour_in_universal
      canonicalGenericEnumerated3Graph U hU A
  exact ⟨(χ v).val, (χ v).property⟩

/-- Forgetting the complete marking produces an ACTUAL
unmarked full finite diary, with no additional leaf and no
arbitrarily chosen ordered presentation. -/
theorem allGenuineUnmarkedDiarySources_nonempty
    {a : Nat} (A : EnumNode a) :
    (allGenuineUnmarkedDiarySources A).Nonempty := by
  classical
  obtain ⟨T,hT⟩ := allGenuineMarkedDiaryFinset_nonempty A
  have hMem : T.source ∈ allGenuineUnmarkedDiarySources A := by
    change T.source ∈
      (allGenuineMarkedDiaryFinset A).image (fun S => S.source)
    exact Finset.mem_image.mpr ⟨T,hT,rfl⟩
  exact ⟨T.source,hMem⟩

/-- Boundary-independent positivity of the genuine full-diary
count aggregated over ALL distinct increasing presentations.
This uses the geometric canonical source, not the terminal
numerical big Ramsey bound or an arbitrary fixed ordering. -/
theorem allIncreasingPresentations_genuineDiarySum_pos
    {a : Nat} (A : EnumNode a) :
    0 < ∑ P ∈ allIncreasingPresentations A,
      (unmarkedDiariesOfIncreasingPresentation A P).card := by
  have hPos : 0 < (allGenuineUnmarkedDiarySources A).card :=
    Finset.card_pos.mpr (allGenuineUnmarkedDiarySources_nonempty A)
  rw [unmarkedDiaryCount_eq_sum_allIncreasingPresentations A] at hPos
  exact hPos

end ATRFiniteDecoder
end ThreeUniformDiaries
