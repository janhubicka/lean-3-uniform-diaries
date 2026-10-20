import ThreeUniformDiaries.DiaryFiniteUniversalEdgeCode
import ThreeUniformDiaries.DiaryFiniteFlipTransitivity
import ThreeUniformDiaries.DiaryFiniteCanonicalFlipPullback
import ThreeUniformDiaries.DiaryFiniteBoundedUniversality
import ThreeUniformDiaries.DiaryFlipCausalInvariantFamily

/-!
# The finite REALIZABLE orbit of diary flips, represented by edge tables

A source diary A has only finitely many possible finite edge tables
on its vertex interval [0,n). The actual diary flips of A form
a finite subset, which need NOT be the full Boolean cube of
one-split and two-split control choices.

This defines that subset literally as finite ternary edge codes,
using the already verified faithful finite flip relation and
its exact Boolean edge-table reconstruction. It proves:

* the baseline code of A belongs to its realised flip family;
* each true flip has a code in the family reconstructing it exactly;
* the family is unchanged when A is replaced by any genuine flip;
* the canonical source flip pulled back from ANY target flip
  has a code in the SAME finite source family;
* a globally injective self-map preserving that family is
  surjective on it, hence has a preimage of the baseline code.

The final invariant-family statement is CONDITIONAL: this
file neither invents independent controls nor asserts the
geometric feedback map is injective, causal, or family-preserving.
Its purpose is to supply the correct genuine finite domain
for the remaining constrained-causality argument.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The exact finite family of *realisable* source flips.
It excludes invalid Boolean ternary tables automatically. -/
noncomputable def finiteSourceFlipCodes
    (A : Ordered3Graph Nat) (n : Nat) :
    Finset (FiniteDiaryEdgeCode n) := by
  classical
  exact Finset.univ.filter
    (fun code => FiniteDiaryFlip A (finiteDiaryCodeGraph n code) n)

/-- A Boolean source edge table belongs to the genuine flip orbit
if and only if the reconstructed finite diary is a flip of A. -/
theorem mem_finiteSourceFlipCodes_iff
    (A : Ordered3Graph Nat) (n : Nat)
    (code : FiniteDiaryEdgeCode n) :
    code ∈ finiteSourceFlipCodes A n ↔
      FiniteDiaryFlip A (finiteDiaryCodeGraph n code) n := by
  classical
  simp [finiteSourceFlipCodes]

/-- The finite orbit is nonempty and contains the literal
finite edge table of its baseline diary. -/
theorem finiteSourceFlipCodes_baseline_mem
    (DA : FiniteRoleDiaryBlock A n) :
    finiteDiaryEdgeCode A n ∈ finiteSourceFlipCodes A n := by
  have hCode : finiteDiaryCodeGraph n (finiteDiaryEdgeCode A n) = A :=
    finiteDiaryCodeGraph_reconstruct A n DA.prediary.frame
  exact (mem_finiteSourceFlipCodes_iff A n
    (finiteDiaryEdgeCode A n)).mpr (by
      rw [hCode]
      exact FiniteDiaryFlip.refl DA)

/-- Every genuine source flip is realised exactly by a member
of the finite code family, with NO spurious artificial vertices
or loss of nonedges. -/
theorem finiteSourceFlipCodes_complete
    (F : FiniteDiaryFlip A P n) :
    ∃ code : FiniteDiaryEdgeCode n,
      code ∈ finiteSourceFlipCodes A n ∧
      finiteDiaryCodeGraph n code = P := by
  let code := finiteDiaryEdgeCode P n
  have hCode : finiteDiaryCodeGraph n code = P :=
    finiteDiaryCodeGraph_reconstruct P n F.target_diary.prediary.frame
  refine ⟨code, ?_, hCode⟩
  exact (mem_finiteSourceFlipCodes_iff A n code).mpr (by
    rw [hCode]
    exact F)

/-- The realised finite flip family is independent of the choice
of baseline within the SAME flip-equivalence class. -/
theorem finiteSourceFlipCodes_eq_of_flip
    (F : FiniteDiaryFlip A P n) :
    finiteSourceFlipCodes A n = finiteSourceFlipCodes P n := by
  classical
  apply Finset.ext
  intro code
  rw [mem_finiteSourceFlipCodes_iff, mem_finiteSourceFlipCodes_iff]
  constructor
  · intro h
    exact F.symm.trans h
  · intro h
    exact F.trans h

/-- The source code obtained by canonical pullback along a bounded
protected embedding after ANY target flip belongs to the genuine,
finite, constrained source-flip family. -/
theorem finiteDiaryPullbackGraph_code_mem_sourceFlips
    {A B B' : Ordered3Graph Nat}
    {n k : Nat} {f : Nat → Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (E : FiniteBoundedMeetEmbedding A B n k f)
    (F : FiniteDiaryFlip B B' k) :
    finiteDiaryEdgeCode (finiteDiaryPullbackGraph B' n f) n ∈
      finiteSourceFlipCodes A n := by
  have hFlip : FiniteDiaryFlip
      A (finiteDiaryPullbackGraph B' n f) n :=
    finiteDiaryPullbackGraph_is_sourceFlip
      DA E.toMeetEmbedding E.image_bound F
  have hCode : finiteDiaryCodeGraph n
      (finiteDiaryEdgeCode (finiteDiaryPullbackGraph B' n f) n) =
        finiteDiaryPullbackGraph B' n f :=
    finiteDiaryCodeGraph_reconstruct
      (finiteDiaryPullbackGraph B' n f) n
      hFlip.target_diary.prediary.frame
  exact (mem_finiteSourceFlipCodes_iff A n _).mpr (by
    rw [hCode]
    exact hFlip)

/-- Finite-orbit correction principle on the ACTUAL constrained
flip tables: any globally injective transformation which closes
this finite family admits a preimage of the prescribed baseline.
The geometric challenge is to supply such a transformation for
the diary construction; this theorem does not assume free bits. -/
theorem exists_realized_flip_code_preimage
    (DA : FiniteRoleDiaryBlock A n)
    (R : FiniteDiaryEdgeCode n → FiniteDiaryEdgeCode n)
    (hInjective : Function.Injective R)
    (hClosed : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteSourceFlipCodes A n →
      R code ∈ finiteSourceFlipCodes A n) :
    ∃ code : FiniteDiaryEdgeCode n,
      code ∈ finiteSourceFlipCodes A n ∧
        R code = finiteDiaryEdgeCode A n := by
  classical
  exact FlipGuidedBranch.exists_preimage_in_invariant_finset
    (finiteSourceFlipCodes A n) R hInjective hClosed
    (finiteDiaryEdgeCode A n)
    (finiteSourceFlipCodes_baseline_mem DA)

end DiaryLeafPriority
end ThreeUniformDiaries
