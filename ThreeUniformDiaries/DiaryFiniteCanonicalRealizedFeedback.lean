import ThreeUniformDiaries.DiaryFiniteCanonicalSourceFlipOrbit
import ThreeUniformDiaries.DiaryFinitePullbackProtectedEmbedding
import ThreeUniformDiaries.DiaryFiniteCanonicalPullbackHitting

/-!
# Genuine geometric feedback on the CANONICAL finite flip orbit

The previous feedback used all Boolean tables on triples, including
duplicate codes differing only on repeated/unordered triples. Its
injectivity condition cannot hold even at the identity target flip.

We instead choose one bounded protected embedding for each
CANONICAL code of a real source flip. Pulling an arbitrary target
flip back along that embedding yields a genuine finite source flip,
whose canonical complete Boolean edge table is again in the same
finite normalized orbit.

In contrast with the raw feedback, the repaired geometric feedback
IS EXACTLY THE IDENTITY when the target is not flipped, independent
of all choices of protected maps. Thus the trivial target-flip
case passes the intended injectivity criterion.

Injectivity for ALL nontrivial target flips remains a substantive
geometric task. This module does not assert it.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A chosen bounded protected copy of each CANONICAL genuine
source flip code in the finite target B. -/
noncomputable def chosenCanonicalSourceFlipMap
    (A B : Ordered3Graph Nat) (n k : Nat)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n}) : Nat → Nat := by
  classical
  exact Classical.choose (hCopies c.val c.property)

/-- The selected map satisfies the full bounded mixed-meet
embedding specification of the actual decoded source flip. -/
theorem chosenCanonicalSourceFlipMap_spec
    (A B : Ordered3Graph Nat) (n k : Nat)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n}) :
    FiniteBoundedMeetEmbedding
      (finiteDiaryCodeGraph n c.val) B n k
      (chosenCanonicalSourceFlipMap A B n k hCopies c) := by
  classical
  exact Classical.choose_spec (hCopies c.val c.property)

/-- Actual canonical feedback: each source flip P is placed in B
by its chosen protected map, and any target flip B' is pulled
back to a true flip Q of P, then encoded CANONICALLY.
Membership of the resulting code is proved via flip transitivity
and faithful finite edge-table reconstruction. -/
noncomputable def realizedCanonicalSourceFlipFeedback
    (A B B' : Ordered3Graph Nat) (n k : Nat)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (F : FiniteDiaryFlip B B' k) :
    {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n} →
    {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n} := by
  classical
  intro c
  let P := finiteDiaryCodeGraph n c.val
  let f := chosenCanonicalSourceFlipMap A B n k hCopies c
  have hRaw : c.val ∈ finiteSourceFlipCodes A n :=
    ((mem_finiteCanonicalSourceFlipCodes_iff A n c.val).mp
      c.property).1
  have FP : FiniteDiaryFlip A P n :=
    (mem_finiteSourceFlipCodes_iff A n c.val).mp hRaw
  have EP : FiniteBoundedMeetEmbedding P B n k f :=
    chosenCanonicalSourceFlipMap_spec A B n k hCopies c
  let Q := finiteDiaryPullbackGraph B' n f
  have FQ : FiniteDiaryFlip P Q n :=
    finiteDiaryPullbackGraph_is_sourceFlip
      FP.target_diary EP.toMeetEmbedding EP.image_bound F
  have FAQ : FiniteDiaryFlip A Q n := FP.trans FQ
  have hQRecon :
      finiteDiaryCodeGraph n (finiteDiaryEdgeCode Q n) = Q :=
    finiteDiaryCodeGraph_reconstruct Q n
      FQ.target_diary.prediary.frame
  have hQCode : finiteDiaryEdgeCode Q n ∈
      finiteCanonicalSourceFlipCodes A n := by
    apply (mem_finiteCanonicalSourceFlipCodes_iff A n _).mpr
    constructor
    · exact (mem_finiteSourceFlipCodes_iff A n _).mpr (by
        rw [hQRecon]
        exact FAQ)
    · unfold IsCanonicalFiniteDiaryEdgeCode
      rw [hQRecon]
  exact ⟨finiteDiaryEdgeCode Q n, hQCode⟩

/-- The value of corrected feedback is the actual Boolean table
of the literal source pullback along its selected bounded map. -/
theorem realizedCanonicalSourceFlipFeedback_val
    (A B B' : Ordered3Graph Nat) (n k : Nat)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (F : FiniteDiaryFlip B B' k)
    (c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n}) :
    (realizedCanonicalSourceFlipFeedback A B B' n k hCopies F c).val =
      finiteDiaryEdgeCode
        (finiteDiaryPullbackGraph B' n
          (chosenCanonicalSourceFlipMap A B n k hCopies c)) n := by
  rfl

/-- Under the IDENTITY target flip, corrected feedback fixes
EVERY canonical source flip code, independent of copy selection. -/
theorem realizedCanonicalSourceFlipFeedback_refl_eq
    (A B : Ordered3Graph Nat) (n k : Nat)
    (DB : FiniteRoleDiaryBlock B k)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n}) :
    realizedCanonicalSourceFlipFeedback A B B n k hCopies
      (FiniteDiaryFlip.refl DB) c = c := by
  let P := finiteDiaryCodeGraph n c.val
  let f := chosenCanonicalSourceFlipMap A B n k hCopies c
  have hRaw : c.val ∈ finiteSourceFlipCodes A n :=
    ((mem_finiteCanonicalSourceFlipCodes_iff A n c.val).mp
      c.property).1
  have FP : FiniteDiaryFlip A P n :=
    (mem_finiteSourceFlipCodes_iff A n c.val).mp hRaw
  have EP : FiniteBoundedMeetEmbedding P B n k f :=
    chosenCanonicalSourceFlipMap_spec A B n k hCopies c
  have hPull : finiteDiaryPullbackGraph B n f = P :=
    (finiteDiaryPullbackGraph_eq_source_iff_boundedEmbedding
      FP.target_diary EP (FiniteDiaryFlip.refl DB)).mpr EP
  have hCanonical :
      finiteDiaryEdgeCode P n = c.val :=
    ((mem_finiteCanonicalSourceFlipCodes_iff A n c.val).mp
      c.property).2
  apply Subtype.ext
  calc
    (realizedCanonicalSourceFlipFeedback A B B n k hCopies
        (FiniteDiaryFlip.refl DB) c).val =
        finiteDiaryEdgeCode (finiteDiaryPullbackGraph B n f) n :=
      realizedCanonicalSourceFlipFeedback_val
        A B B n k hCopies (FiniteDiaryFlip.refl DB) c
    _ = finiteDiaryEdgeCode P n := congrArg
      (fun X : Ordered3Graph Nat => finiteDiaryEdgeCode X n) hPull
    _ = c.val := hCanonical

/-- In particular, the repaired feedback IS INJECTIVE for the
unflipped target. This failed on the old noncanonical raw orbit. -/
theorem realizedCanonicalSourceFlipFeedback_refl_injective
    (A B : Ordered3Graph Nat) (n k : Nat)
    (DB : FiniteRoleDiaryBlock B k)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f) :
    Function.Injective
      (realizedCanonicalSourceFlipFeedback A B B n k hCopies
        (FiniteDiaryFlip.refl DB)) := by
  intro c d h
  calc
    c = realizedCanonicalSourceFlipFeedback A B B n k hCopies
          (FiniteDiaryFlip.refl DB) c :=
        (realizedCanonicalSourceFlipFeedback_refl_eq
          A B n k DB hCopies c).symm
    _ = realizedCanonicalSourceFlipFeedback A B B n k hCopies
          (FiniteDiaryFlip.refl DB) d := h
    _ = d := realizedCanonicalSourceFlipFeedback_refl_eq
      A B n k DB hCopies d

end DiaryLeafPriority
end ThreeUniformDiaries
