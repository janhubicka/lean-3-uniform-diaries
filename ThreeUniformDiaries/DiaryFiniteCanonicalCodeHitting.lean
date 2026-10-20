import ThreeUniformDiaries.DiaryFiniteSourceFlipCodeOrbit
import ThreeUniformDiaries.DiaryFiniteCanonicalPullbackHitting

/-!
# A finite Boolean-code criterion for surviving prescribed target flips

The canonical source pullback of a finite target flip is an actual
realisable source diary flip, and its FULL bounded ternary edge
table is a member of the verified finiteSourceFlipCodes orbit.

The exact same-map survival criterion can therefore be expressed
as equality of two FINITE BOOLEAN EDGE CODES, rather than as
equality of abstract ordered graph predicates on all Nat.
This is the correct finite object for searching a family of
copies that is guaranteed to contain an unflipped source under
every target flip.

The result does not prove that such a protected hitting family
exists. It also does not assume that the real flip orbit is the
full cube of free independent split-control bits.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A B B' : Ordered3Graph Nat} {n k : Nat} {f : Nat → Nat}

/-- Finite exact graph equality of the canonical source pullback
is equivalent to equality of its FULL finite Boolean edge table
with the baseline source table. The canonical pullback and source
are both bounded finite frames, so reconstruction is faithful. -/
theorem finiteDiaryPullbackGraph_code_eq_source_iff
    (DA : FiniteRoleDiaryBlock A n)
    (E : FiniteBoundedMeetEmbedding A B n k f)
    (F : FiniteDiaryFlip B B' k) :
    finiteDiaryEdgeCode (finiteDiaryPullbackGraph B' n f) n =
        finiteDiaryEdgeCode A n ↔
      finiteDiaryPullbackGraph B' n f = A := by
  let P := finiteDiaryPullbackGraph B' n f
  have FP : FiniteDiaryFlip A P n :=
    finiteDiaryPullbackGraph_is_sourceFlip
      DA E.toMeetEmbedding E.image_bound F
  have hP : finiteDiaryCodeGraph n (finiteDiaryEdgeCode P n) = P :=
    finiteDiaryCodeGraph_reconstruct P n
      FP.target_diary.prediary.frame
  have hA : finiteDiaryCodeGraph n (finiteDiaryEdgeCode A n) = A :=
    finiteDiaryCodeGraph_reconstruct A n DA.prediary.frame
  constructor
  · intro hCode
    change finiteDiaryEdgeCode P n = finiteDiaryEdgeCode A n at hCode
    change P = A
    calc
      P = finiteDiaryCodeGraph n (finiteDiaryEdgeCode P n) := hP.symm
      _ = finiteDiaryCodeGraph n (finiteDiaryEdgeCode A n) :=
        congrArg (finiteDiaryCodeGraph n) hCode
      _ = A := hA
  · intro hGraph
    exact congrArg (fun G : Ordered3Graph Nat =>
      finiteDiaryEdgeCode G n) hGraph

/-- The Boolean code of the canonical source flip equals the
baseline source code iff the fixed bounded copy of A survives
this arbitrary target flip as a FULL meet embedding. -/
theorem finiteDiaryPullbackGraph_code_eq_source_iff_embedding
    (DA : FiniteRoleDiaryBlock A n)
    (E : FiniteBoundedMeetEmbedding A B n k f)
    (F : FiniteDiaryFlip B B' k) :
    finiteDiaryEdgeCode (finiteDiaryPullbackGraph B' n f) n =
        finiteDiaryEdgeCode A n ↔
      FiniteBoundedMeetEmbedding A B' n k f := by
  exact (finiteDiaryPullbackGraph_code_eq_source_iff DA E F).trans
    (finiteDiaryPullbackGraph_eq_source_iff_boundedEmbedding DA E F)

/-- With a prescribed finite family of bounded copies of A in B,
the condition that at least one copy remains fully embedded in
EVERY target flip is equivalent to hitting the literal baseline
source Boolean edge code via canonical pullbacks. -/
theorem finite_copy_family_survival_iff_code_hits
    (DA : FiniteRoleDiaryBlock A n)
    (X : Finset (Nat → Nat))
    (hCopies : ∀ g : Nat → Nat, g ∈ X →
      FiniteBoundedMeetEmbedding A B n k g) :
    (∀ T : Ordered3Graph Nat, FiniteDiaryFlip B T k →
      ∃ g : Nat → Nat, g ∈ X ∧
        FiniteBoundedMeetEmbedding A T n k g) ↔
    (∀ T : Ordered3Graph Nat, FiniteDiaryFlip B T k →
      ∃ g : Nat → Nat, g ∈ X ∧
        finiteDiaryEdgeCode (finiteDiaryPullbackGraph T n g) n =
          finiteDiaryEdgeCode A n) := by
  constructor
  · intro h T FT
    obtain ⟨g,hg,hE⟩ := h T FT
    exact ⟨g,hg,
      (finiteDiaryPullbackGraph_code_eq_source_iff_embedding
        DA (hCopies g hg) FT).mpr hE⟩
  · intro h T FT
    obtain ⟨g,hg,hCode⟩ := h T FT
    exact ⟨g,hg,
      (finiteDiaryPullbackGraph_code_eq_source_iff_embedding
        DA (hCopies g hg) FT).mp hCode⟩

/-- A range-correct every-target-flip absorption certificate can
be presented as a finite family of genuine protected copies whose
canonical pullback codes hit the baseline code under every target
flip. This theorem is only a CORRECT sufficient criterion. -/
theorem absorbsEveryTargetFlipInside_of_finite_code_hits
    (DA : FiniteRoleDiaryBlock A n)
    (X : Finset (Nat → Nat))
    (hCopies : ∀ g : Nat → Nat, g ∈ X →
      FiniteBoundedMeetEmbedding A B n k g)
    (hHits : ∀ T : Ordered3Graph Nat, FiniteDiaryFlip B T k →
      ∃ g : Nat → Nat, g ∈ X ∧
        finiteDiaryEdgeCode (finiteDiaryPullbackGraph T n g) n =
          finiteDiaryEdgeCode A n) :
    AbsorbsEveryTargetFlipInside A B n k := by
  intro T FT
  obtain ⟨g,hg,hEq⟩ := hHits T FT
  exact ⟨g,
    (finiteDiaryPullbackGraph_code_eq_source_iff_embedding
      DA (hCopies g hg) FT).mp hEq⟩

end DiaryLeafPriority
end ThreeUniformDiaries
