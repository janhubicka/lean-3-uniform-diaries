import ThreeUniformDiaries.DiaryFinitePairColour
import ThreeUniformDiaries.DiaryFiniteSingletonColour
import ThreeUniformDiaries.TwoTypeMeetLevel

/-!
# Track A: exact capped S2 meet as a FINITE full pair-type colour boundary

A full ordered-pair type below cut B has three independent finite
sets of tests:
  (1) complete singleton bits of the first coordinate;
  (2) complete singleton bits of the second coordinate;
  (3) auxiliary bits E(x,first,second) for x<B.

The three-component finite colour below B agrees for two pairs
exactly when their full SameTwoTypeBelow B predicate agrees.

The full numerical S2 meet is the LAST common cut, CAPPED at the
smaller first-coordinate vertex. Hence exact value t is equivalent
to colour agreement at t and either:
  * t is already the pair-type cap; or
  * the full colours disagree at t+1.
The cap alternative is essential: there may be agreement beyond t
while the capped meet is still exactly t.

This provides a finite Boolean-code interface for the complete S2
numeric meet, complementing the exact S1 two-cut test already merged.
It supplies no protected target candidate, persistent successor,
countable unavoidability, or diary Ramsey theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A FINITE full 2-type code: two finite singleton masks and all
auxiliary bit tests. No lex-orientation bit is needed for the
SameTwoTypeBelow predicate and numeric S2 meet. -/
noncomputable def fullTwoTypeColour
    (K : Ordered3Graph Nat) (B u₀ u₁ : Nat) :
    ((Fin B → Fin B → Bool) × (Fin B → Fin B → Bool)) ×
      (Fin B → Bool) :=
  ((DiaryLowerBoundColors.singletonColour K B u₀,
    DiaryLowerBoundColors.singletonColour K B u₁),
    fun z => decide (K.edge z.val u₀ u₁))

/-- This finite code is EXACTLY agreement of the full two type:
both coordinate singleton types and the auxiliary pair type. -/
theorem fullTwoTypeColour_eq_iff_sameTwoTypeBelow
    (K : Ordered3Graph Nat) (B u₀ u₁ v₀ v₁ : Nat) :
    fullTwoTypeColour K B u₀ u₁ =
      fullTwoTypeColour K B v₀ v₁ ↔
      K.SameTwoTypeBelow B u₀ u₁ v₀ v₁ := by
  classical
  constructor
  · intro h
    have hFirst :
        DiaryLowerBoundColors.singletonColour K B u₀ =
        DiaryLowerBoundColors.singletonColour K B v₀ :=
      congrArg (fun c => c.1.1) h
    have hSecond :
        DiaryLowerBoundColors.singletonColour K B u₁ =
        DiaryLowerBoundColors.singletonColour K B v₁ :=
      congrArg (fun c => c.1.2) h
    have hAux :
        (fun z : Fin B => decide (K.edge z.val u₀ u₁)) =
        (fun z : Fin B => decide (K.edge z.val v₀ v₁)) :=
      congrArg (fun c => c.2) h
    refine ⟨(DiaryLowerBoundColors.singletonColour_eq_iff
      K B u₀ v₀).mp hFirst,
      (DiaryLowerBoundColors.singletonColour_eq_iff
        K B u₁ v₁).mp hSecond, ?_⟩
    intro x hx
    have hBit := congrFun hAux (⟨x, hx⟩ : Fin B)
    change decide (K.edge x u₀ u₁) =
      decide (K.edge x v₀ v₁) at hBit
    by_cases hE : K.edge x u₀ u₁
    · have hV : K.edge x v₀ v₁ := by
        by_contra hNo
        simp [hE, hNo] at hBit
      exact iff_of_true hE hV
    · have hV : ¬ K.edge x v₀ v₁ := by
        intro hYes
        simp [hE, hYes] at hBit
      exact iff_of_false hE hV
  · rintro ⟨hFirst, hSecond, hAux⟩
    apply Prod.ext
    · apply Prod.ext
      · exact (DiaryLowerBoundColors.singletonColour_eq_iff
          K B u₀ v₀).mpr hFirst
      · exact (DiaryLowerBoundColors.singletonColour_eq_iff
          K B u₁ v₁).mpr hSecond
    · funext z
      have hE : K.edge z.val u₀ u₁ ↔
          K.edge z.val v₀ v₁ := hAux z.isLt
      by_cases hU : K.edge z.val u₀ u₁
      · have hV : K.edge z.val v₀ v₁ := hE.mp hU
        simp [fullTwoTypeColour, hU, hV]
      · have hV : ¬ K.edge z.val v₀ v₁ := by
          intro h
          exact hU (hE.mpr h)
        simp [fullTwoTypeColour, hU, hV]

/-- Exact capped full-pair S2 meet is equivalent to a finite
two-cut colour test, EXCEPT that t=cap itself also suffices.

Unlike a naive first-difference formula, this statement handles
the cap case correctly, without full RoleDiary or leaf hypotheses. -/
theorem twoMeetLevel_eq_iff_fullTwoTypeColour_boundary_or_cap
    (K : Ordered3Graph Nat)
    (u₀ u₁ v₀ v₁ t : Nat) :
    K.twoMeetLevel u₀ u₁ v₀ v₁ = t ↔
    t ≤ min u₀ v₀ ∧
    fullTwoTypeColour K t u₀ u₁ =
      fullTwoTypeColour K t v₀ v₁ ∧
    (t = min u₀ v₀ ∨
      fullTwoTypeColour K (t + 1) u₀ u₁ ≠
        fullTwoTypeColour K (t + 1) v₀ v₁) := by
  classical
  constructor
  · intro hMeet
    have hCap : t ≤ min u₀ v₀ := by
      rw [← hMeet]
      exact K.twoMeetLevel_le_min u₀ u₁ v₀ v₁
    have hAt : K.SameTwoTypeBelow t u₀ u₁ v₀ v₁ := by
      rw [← hMeet]
      exact K.twoMeetLevel_agree u₀ u₁ v₀ v₁
    refine ⟨hCap, (fullTwoTypeColour_eq_iff_sameTwoTypeBelow
      K t u₀ u₁ v₀ v₁).mpr hAt, ?_⟩
    by_cases hAtCap : t = min u₀ v₀
    · exact Or.inl hAtCap
    · right
      intro hNextEq
      have hNext : K.SameTwoTypeBelow (t + 1) u₀ u₁ v₀ v₁ :=
        (fullTwoTypeColour_eq_iff_sameTwoTypeBelow
          K (t + 1) u₀ u₁ v₀ v₁).mp hNextEq
      have hInCap : t + 1 ≤ min u₀ v₀ := by omega
      have hTooHigh : t + 1 ≤ K.twoMeetLevel u₀ u₁ v₀ v₁ :=
        Nat.le_findGreatest hInCap hNext
      omega
  · rintro ⟨hCap, hAt, hEnd⟩
    have hAtType : K.SameTwoTypeBelow t u₀ u₁ v₀ v₁ :=
      (fullTwoTypeColour_eq_iff_sameTwoTypeBelow
        K t u₀ u₁ v₀ v₁).mp hAt
    have hLower : t ≤ K.twoMeetLevel u₀ u₁ v₀ v₁ :=
      Nat.le_findGreatest hCap hAtType
    have hUpper : K.twoMeetLevel u₀ u₁ v₀ v₁ ≤ t := by
      rcases hEnd with hEqualsCap | hDifferent
      · have hMax := K.twoMeetLevel_le_min u₀ u₁ v₀ v₁
        omega
      · by_contra hNo
        have hPast : t + 1 ≤ K.twoMeetLevel u₀ u₁ v₀ v₁ := by
          omega
        have hAgrees := K.twoMeetLevel_agree u₀ u₁ v₀ v₁
        have hAtNext :
            K.SameTwoTypeBelow (t + 1) u₀ u₁ v₀ v₁ := by
          refine ⟨?_, ?_, ?_⟩
          · intro x y hxy hy
            exact hAgrees.1 hxy (lt_of_lt_of_le hy hPast)
          · intro x y hxy hy
            exact hAgrees.2.1 hxy (lt_of_lt_of_le hy hPast)
          · intro x hx
            exact hAgrees.2.2 (lt_of_lt_of_le hx hPast)
        have hNextEq :
            fullTwoTypeColour K (t + 1) u₀ u₁ =
            fullTwoTypeColour K (t + 1) v₀ v₁ :=
          (fullTwoTypeColour_eq_iff_sameTwoTypeBelow
            K (t + 1) u₀ u₁ v₀ v₁).mpr hAtNext
        exact hDifferent hNextEq
    exact Nat.le_antisymm hUpper hLower

end DiaryLeafPriority
end ThreeUniformDiaries
