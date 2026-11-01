import ThreeUniformDiaries.DiaryUpperBoundGenuineMarkedFamily
import ThreeUniformDiaries.DiaryFiniteAutTorsor

/-!
# Track A: the markings of ONE genuine finite diary are an Aut(A) torsor

The candidate sharp diary-count formula includes a factor
|Aut(A)|. This must not be inserted by a blanket appeal to
labelled/unlabelled copies: the actual source objects carry
distinguished leaf positions and a full finite V/E/S diagram.

For a fixed full finite diary source S, any two markings
that both represent a labelled induced copy of the same A
and BOTH exhaust the genuine leaf set differ by precisely
one source automorphism of A. In particular the underlying
finite full diary diagram is unchanged.

This is the exact fibrewise torsor statement needed to
count marked source types. It uses the verified general
finite labelled-copy torsor from Track C PR #990 and the
full-leaf coverage condition of the genuine marked family.
No big Ramsey assertion or countable unavoidability occurs.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- Two genuine markings of the SAME finite diary source are
related by exactly one finite unordered automorphism of A.
Every marked coordinate remains an actual source leaf and
the two markings cover exactly the same source leaf set. -/
theorem genuineMarkedDiaryShape_unique_aut_between_markings
    {a : Nat} (A : EnumNode a)
    (S : ProtectedSource 0)
    (p q : Fin a → Fin (S.k + 1))
    (hp : IsGenuineMarkedDiaryShape A ⟨S, p⟩)
    (hq : IsGenuineMarkedDiaryShape A ⟨S, q⟩) :
    ∃! σ : FiniteHypergraphAut A.toOrdered3Graph a,
      ∀ i : Fin a, (q i).val = (p (σ.val i)).val := by
  dsimp [IsGenuineMarkedDiaryShape] at hp hq
  obtain ⟨_, hpCopy, hpLeaf, hpCover⟩ := hp
  obtain ⟨_, hqCopy, hqLeaf, hqCover⟩ := hq
  have hSameRange :
      Set.range (fun i : Fin a => (p i).val) =
        Set.range (fun i : Fin a => (q i).val) := by
    ext u
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj⟩ :=
        hqCover (p i).val (hpLeaf i).1
          (p i).isLt (hpLeaf i)
      exact ⟨j, hj⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj⟩ :=
        hpCover (q i).val (hqLeaf i).1
          (q i).isLt (hqLeaf i)
      exact ⟨j, hj⟩
  exact finiteLabelledCopy_unique_automorphism
    hpCopy hqCopy hSameRange

end ATRFiniteDecoder
end ThreeUniformDiaries
