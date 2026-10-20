import ThreeUniformDiaries.DiaryFinitePullbackProtectedEmbedding
import ThreeUniformDiaries.DiaryFiniteBoundedUniversality

/-!
# Exact criterion for a prescribed copy to survive a target flip

Given a genuine bounded finite meet embedding f : A -> B, and
a target flip B' of B, the canonical induced pullback P of B'
along f is already known to be a genuine flip of A and to
embed with all meets into B' (#797).

This module isolates the remaining exact question:
does the given map f embed the ORIGINAL unflipped A into B'?
The answer is YES precisely when the canonical pullback
P is literally A, as a finite ordered ternary edge table.

As a consequence, a finite family of protected copies of A in B
witnesses absorption in every target flip whenever at least one
canonical pullback in that family equals A for every target flip.
This is a conditional, FINITE combinatorial hitting criterion,
not an existence proof for such a family.

In particular, the source flip found in #797 may depend on B'.
Nothing here identifies that source flip with A in general.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A B B' : Ordered3Graph Nat} {n k : Nat} {f : Nat → Nat}

/-- An original bounded copy survives a target flip along the SAME
map if and only if its canonical induced finite source pullback is
literally the original source A. This uses the verified exact
mixed-meet transport, not an invalid assumption that inducedness
alone transports arbitrary meets across omitted vertices. -/
theorem finiteDiaryPullbackGraph_eq_source_iff_boundedEmbedding
    (DA : FiniteRoleDiaryBlock A n)
    (E : FiniteBoundedMeetEmbedding A B n k f)
    (F : FiniteDiaryFlip B B' k) :
    finiteDiaryPullbackGraph B' n f = A ↔
      FiniteBoundedMeetEmbedding A B' n k f := by
  constructor
  · intro hEq
    simpa only [hEq] using
      (finiteDiaryPullbackGraph_boundedEmbedding_into_targetFlip
        DA E F)
  · intro E'
    apply finiteDiaryPullbackGraph_unique
      B' n f A DA.prediary.frame
    intro a b c hab hbc hcn
    exact (E'.toMeetEmbedding.edge_iff a b c hab hbc hcn).symm

/-- For a PRESCRIBED finite collection of protected source copies
in B, the property that one of these same maps embeds A into
every target flip is equivalent to the canonical pullbacks from
that collection hitting the baseline source A in every target flip.

Neither direction produces this hitting collection: the theorem
only identifies the exact condition needed in a finite causal
flip-family argument. -/
theorem finite_copy_family_survives_iff_pullback_hits
    (DA : FiniteRoleDiaryBlock A n)
    (X : Finset (Nat → Nat))
    (hCopies : ∀ g : Nat → Nat, g ∈ X →
      FiniteBoundedMeetEmbedding A B n k g) :
    (∀ T : Ordered3Graph Nat, FiniteDiaryFlip B T k →
      ∃ g : Nat → Nat, g ∈ X ∧
        FiniteBoundedMeetEmbedding A T n k g) ↔
    (∀ T : Ordered3Graph Nat, FiniteDiaryFlip B T k →
      ∃ g : Nat → Nat, g ∈ X ∧
        finiteDiaryPullbackGraph T n g = A) := by
  constructor
  · intro h T FT
    obtain ⟨g,hg,hEg⟩ := h T FT
    exact ⟨g,hg,
      (finiteDiaryPullbackGraph_eq_source_iff_boundedEmbedding
        DA (hCopies g hg) FT).mpr hEg⟩
  · intro h T FT
    obtain ⟨g,hg,hEq⟩ := h T FT
    exact ⟨g,hg,
      (finiteDiaryPullbackGraph_eq_source_iff_boundedEmbedding
        DA (hCopies g hg) FT).mp hEq⟩

/-- Sufficient condition for the STRONG, range-correct every-flip
absorption statement: some member of a fixed finite family of
protected source copies must pull back literally to A in every
target flip. No false independence of split control bits is
assumed here. -/
theorem absorbsEveryTargetFlipInside_of_finite_pullback_hits
    (DA : FiniteRoleDiaryBlock A n)
    (X : Finset (Nat → Nat))
    (hCopies : ∀ g : Nat → Nat, g ∈ X →
      FiniteBoundedMeetEmbedding A B n k g)
    (hHits : ∀ T : Ordered3Graph Nat, FiniteDiaryFlip B T k →
      ∃ g : Nat → Nat, g ∈ X ∧
        finiteDiaryPullbackGraph T n g = A) :
    AbsorbsEveryTargetFlipInside A B n k := by
  intro T FT
  obtain ⟨g,hg,hEg⟩ := hHits T FT
  exact ⟨g, (finiteDiaryPullbackGraph_eq_source_iff_boundedEmbedding
    DA (hCopies g hg) FT).mp hEg⟩

end DiaryLeafPriority
end ThreeUniformDiaries
