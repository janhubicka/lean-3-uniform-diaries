import ThreeUniformDiaries.DiaryOnePassFullProtectedPrefix
import ThreeUniformDiaries.DiaryNoCountableLiteralFiniteFullPrefix
import Lean.Elab.Tactic.Omega

/-!
# Track B: a FULL finite diary prefix forces an actual one-pass insertion

A global RolePrediary H may carry the literal complete edge/nonedge
prefix of some genuine finite FULL diary A on [0,n). But completing
H to a genuine countable RoleDiary by the actual one-pass procedure
CANNOT leave that ENTIRE complete finite prefix literally fixed.

Indeed no finite full diary of size >=4 can be a literal prefix
of ANY full countable diary (verified #1403). The previously checked
one-pass event criterion (verified #1389/#1401) says that a literal
fixed prefix occurs exactly when there are no scheduled event blocks
at its source indices. Thus there MUST exist some TRUE nonmarker
old index 3 <= m < n with a NONEMPTY event block, and its old-image
numerical rank moves strictly forward.

This is a negative constraint for the still OPEN relative absorber
extension: protected cuts must be PROPER incomplete diagrams and
cannot contain a complete finite FULL diary. It does not rule out
protected proper prefixes or moving exact-meet embeddings.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- No countable RolePrediary with a prescribed complete FULL
finite diary old-prefix can have a one-pass schedule devoid of
new events before that ENTIRE old finite frame. -/
theorem fullFiniteDiaryPrefix_forces_onePass_event
    {A H : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (PH : RolePrediary H)
    (hn : 4 ≤ n)
    (hAH : LiteralOldPrefixAgreement A H n) :
    ¬ OnePassNoEventsBelow H n := by
  intro hNo
  have hHK : LiteralOldPrefixAgreement H (onePassRawTarget H) n :=
    onePass_noEvents_literalOldPrefix PH n hNo
  have hAK : LiteralOldPrefixAgreement A (onePassRawTarget H) n := by
    intro a b c hc
    exact (hAH a b c hc).trans (hHK a b c hc)
  exact no_literal_full_finite_diary_prefix_in_countable
    DA (onePassRawTarget_isDiary PH) hn hAK

/-- The above obstruction has a concrete finite witness:
an actual one-/two-event block inserted at a nonmarker old
index in the complete finite FULL diary prefix, moving
that original vertex strictly to the right. -/
theorem fullFiniteDiaryPrefix_exists_moving_onePass_block
    {A H : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (PH : RolePrediary H)
    (hn : 4 ≤ n)
    (hAH : LiteralOldPrefixAgreement A H n) :
    ∃ m : Nat, 3 ≤ m ∧ m < n ∧
      0 < onePassBlockSize H m ∧ m < onePassOldImage H m := by
  have hNot := fullFiniteDiaryPrefix_forces_onePass_event
    DA PH hn hAH
  have hExists : ∃ m : Nat, m < n ∧
      onePassBlockSize H m ≠ 0 := by
    by_contra hEmpty
    apply hNot
    intro m hm
    by_contra hNE
    exact hEmpty ⟨m,hm,hNE⟩
  obtain ⟨m,hm,hNE⟩ := hExists
  have hm3 : 3 ≤ m := by
    by_contra hSmall
    have hmSmall : m < 3 := by omega
    have hZero : onePassBlockSize H m = 0 := by
      simp [onePassBlockSize, onePassBlock_markers H m hmSmall]
    exact hNE hZero
  have hPos : 0 < onePassBlockSize H m := by omega
  exact ⟨m,hm3,hm,hPos,
    onePassOldImage_moves_of_nonzeroBlock H m hPos⟩

end DiaryLeafPriority
end ThreeUniformDiaries
