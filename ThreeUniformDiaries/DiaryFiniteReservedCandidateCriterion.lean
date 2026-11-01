import ThreeUniformDiaries.DiaryFiniteCandidateCriterion
import ThreeUniformDiaries.DiaryFutureOrderReserve

/-!
# Exact finite test for a relative successor retaining future order capacity

The finite generator-table criterion for one prescribed target leaf
image v has already isolated the role, induced-edge, singleton-meet,
full-pair-meet and leaf-range tests. A coherent countable embedding
additionally requires enough numerical room for source vertices that
have not yet entered the finite support.

The previously verified FutureOrderReserve predicate is a FINITE
condition on the generated support and its map. We prove that a
relative successor satisfying this reserve exists exactly when one
candidate target leaf v satisfies the existing finite table criterion
AND this same finite reserve on the table-induced map.

No existence of an appropriate v is asserted. In particular this
theorem is not countable diary unavoidability, and neither finite
flip absorption nor genericity is used to produce a target leaf.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace AdmissibleCofinalDiaryStage

variable {H K : Ordered3Graph Nat}
variable {F f : Nat → Nat} {m : Nat}

/-- For a FIXED proposed new target leaf image v, the complete
relative successor and quantitative future-spacing requirements
are equivalent to two finite checks on the candidate table. -/
theorem reserved_successor_iff_finite_reserved_candidate
    (DH : RoleDiary H)
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (v : Nat) :
    (∃ g : Nat → Nat,
      AdmissibleCofinalDiaryStage H K F (m + 1) g ∧
      (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
        g a = f a) ∧
      g m = v ∧
      FutureOrderReserve H (m + 1) g) ↔
    (FiniteNewLeafCandidateCondition H K F m f v ∧
      FutureOrderReserve H (m + 1)
        (candidateNewLeafTableMap H K m f v)) := by
  constructor
  · rintro ⟨g,Q,hKeep,hNew,hReserve⟩
    have hCandidate :
        FiniteNewLeafCandidateCondition H K F m f v :=
      (relative_successor_iff_finite_candidate DH P hm v).mp
        ⟨g,Q,hKeep,hNew⟩
    refine ⟨hCandidate, ?_⟩
    intro x y hx hy hxy
    have hX :
        candidateNewLeafTableMap H K m f v x = g x :=
      Q.relative_successor_agrees_with_table hKeep hNew x hx
    have hY :
        candidateNewLeafTableMap H K m f v y = g y :=
      Q.relative_successor_agrees_with_table hKeep hNew y hy
    simpa only [hX,hY] using hReserve x y hx hy hxy
  · rintro ⟨hCandidate,hReserve⟩
    obtain ⟨g,Q,hKeep,hNew⟩ :=
      (relative_successor_iff_finite_candidate DH P hm v).mpr
        hCandidate
    refine ⟨g,Q,hKeep,hNew,?_⟩
    intro x y hx hy hxy
    have hX :
        candidateNewLeafTableMap H K m f v x = g x :=
      Q.relative_successor_agrees_with_table hKeep hNew x hx
    have hY :
        candidateNewLeafTableMap H K m f v y = g y :=
      Q.relative_successor_agrees_with_table hKeep hNew y hy
    simpa only [hX,hY] using hReserve x y hx hy hxy

/-- An explicit FINITE-CANDIDATE realization predicate precisely
characterizes existence of some reserved relative successor. The
quantifier over possible target leaf images v is still an open
realization problem; this statement neither removes that quantifier
nor constructs a witness. -/
theorem exists_reserved_successor_iff_finite_reserved_candidate
    (DH : RoleDiary H)
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m) :
    (∃ g : Nat → Nat,
      AdmissibleCofinalDiaryStage H K F (m + 1) g ∧
      (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
        g a = f a) ∧
      FutureOrderReserve H (m + 1) g) ↔
    (∃ v : Nat,
      FiniteNewLeafCandidateCondition H K F m f v ∧
      FutureOrderReserve H (m + 1)
        (candidateNewLeafTableMap H K m f v)) := by
  constructor
  · rintro ⟨g,Q,hKeep,hReserve⟩
    refine ⟨g m,?_⟩
    exact (reserved_successor_iff_finite_reserved_candidate
      DH P hm (g m)).mp ⟨g,Q,hKeep,rfl,hReserve⟩
  · rintro ⟨v,hCandidate⟩
    obtain ⟨g,Q,hKeep,hNew,hReserve⟩ :=
      (reserved_successor_iff_finite_reserved_candidate
        DH P hm v).mpr hCandidate
    exact ⟨g,Q,hKeep,hReserve⟩

end AdmissibleCofinalDiaryStage
end DiaryLeafPriority
end ThreeUniformDiaries
