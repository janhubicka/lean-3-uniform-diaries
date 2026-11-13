import ThreeUniformDiaries.DiaryDummyTailFiniteEventFreeTest
import ThreeUniformDiaries.DiaryFullPrefixMustOnePassMove
import ThreeUniformDiaries.DiaryEventFreePrediaryFiniteCompletion
import Lean.Elab.Tactic.Omega

/-!
# Track B: full finite diaries obstruct event-free dummy-tail completion

The verified finiteDummyTailCarrier retains the literal OLD finite
edge/nonedge table of any genuine finite diary block H on [0,n).
The verified dummy-tail prediary theorem obtains some Boolean
cross orientation bits making this countable carrier a genuine
global RolePrediary.

The newer exact finite census computes whether its actual one-pass
completion inserts no events below a prescribed old cut. The
previously verified countable no-literal-FULL-diary-prefix
obstruction shows that for p=n this test CANNOT pass whenever
the dummy-tail carrier is a genuine RolePrediary.

This is an adversarial check on a possible false route to protected
absorbers: applying the event-free test to the ENTIRE full finite
old block is infeasible, regardless of how the causal cross bits
are selected. The protected cut must leave an INCOMPLETE old tail.

These are conditional impossibility and witness statements.
They do NOT construct a proper protected relative prediary,
a bounded selected absorber tower, or countable flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- An ACTUAL finite selected-germ compatibility certificate,
together with a SUPPLIED global dummy-tail RolePrediary, yields a
genuine full finite diary protecting every old vertex below a
(possibly proper) cut p<=n, including all exact old numeric meets.
The existence of suitable cross bits and a suitable prediary is
not provided by this conditional theorem. -/
theorem finiteDummyTail_finiteTest_yields_fullFiniteRelativeCompletion
    {H : Ordered3Graph Nat} {n : Nat}
    (PH : FiniteRolePrediaryBlock H n)
    (bits : Nat → Bool)
    (PT : RolePrediary (finiteDummyTailCarrier H n bits))
    (p : Nat) (hp : p ≤ n)
    (hFinite : FiniteDummyTailEventFreeTest H n bits p) :
    ∃ (C : Ordered3Graph Nat) (m : Nat),
      FiniteRoleDiaryBlock C m ∧
      p < m ∧
      LiteralOldPrefixAgreement H C p ∧
      (∀ u : Nat, u < p →
        (IsLeaf H u ↔ IsLeaf C u) ∧
        (IsOneSplit H u ↔ IsOneSplit C u) ∧
        (IsTwoSplit H u ↔ IsTwoSplit C u)) ∧
      (∀ u v : Nat, u < p → v < p →
        H.oneMeetLevel u v = C.oneMeetLevel u v) ∧
      (∀ a b c d : Nat, a < p → b < p → c < p → d < p →
        H.twoMeetLevel a b c d = C.twoMeetLevel a b c d) ∧
      (IsLeaf C (m-1) ∧ p ≤ m-1) := by
  have hNoEvents :
      OnePassNoEventsBelow (finiteDummyTailCarrier H n bits) p :=
    (finiteDummyTail_noEventsBelow_iff_finiteTest
      H n PH.frame bits p hp).mpr hFinite
  obtain ⟨C,m,DC,hpm,hTailC,_hRoles,_hOne,_hTwo,hLast⟩ :=
    exists_finiteFullDiary_retaining_eventFree_prediary_prefix
      PT p hNoEvents
  have hOldTail :
      LiteralOldPrefixAgreement H (finiteDummyTailCarrier H n bits) p := by
    intro a b c hc
    exact (finiteDummyTailCarrier_finite_edge_iff
      PH.frame bits a b c (lt_of_lt_of_le hc hp)).symm
  have hOldC : LiteralOldPrefixAgreement H C p := by
    intro a b c hc
    exact (hOldTail a b c hc).trans (hTailC a b c hc)
  refine ⟨C,m,DC,hpm,hOldC,?_,?_,?_,hLast⟩
  · intro u hu
    exact role_iff_of_literalOldPrefix hOldC u hu
  · intro u v hu hv
    exact oneMeetLevel_eq_of_literalOldPrefix hOldC u v hu hv
  · intro a b c d ha hb hc hd
    exact twoMeetLevel_eq_of_literalOldPrefix
      hOldC a b c d ha hb hc hd

/-- A GLOBAL dummy-tail prediary extending an actual full finite
diary cannot have an event-free one-pass schedule on the entire
old finite frame. The exact finite old/tail germ test is
therefore necessarily false for the full cut p=n. -/
theorem finiteDummyTail_fullDiary_no_fullFrameEventFree
    {H : Ordered3Graph Nat} {n : Nat}
    (DH : FiniteRoleDiaryBlock H n)
    (hn : 4 ≤ n)
    (bits : Nat → Bool)
    (PT : RolePrediary (finiteDummyTailCarrier H n bits)) :
    ¬ FiniteDummyTailEventFreeTest H n bits n := by
  have hPrefix :
      LiteralOldPrefixAgreement H (finiteDummyTailCarrier H n bits) n := by
    intro a b c hc
    exact (finiteDummyTailCarrier_finite_edge_iff
      DH.prediary.frame bits a b c hc).symm
  have hNo : ¬ OnePassNoEventsBelow
      (finiteDummyTailCarrier H n bits) n :=
    fullFiniteDiaryPrefix_forces_onePass_event
      DH PT hn hPrefix
  intro hFiniteTest
  exact hNo ((finiteDummyTail_noEventsBelow_iff_finiteTest
    H n DH.prediary.frame bits n (le_refl n)).mpr hFiniteTest)

/-- There is no choice of actual old-to-tail Devlin orientation
which BOTH forms a genuine global RolePrediary and passes the
full-frame finite event-free selected-germ compatibility test. -/
theorem finiteDummyTail_fullDiary_no_valid_eventFree_bits
    {H : Ordered3Graph Nat} {n : Nat}
    (DH : FiniteRoleDiaryBlock H n)
    (hn : 4 ≤ n) :
    ¬ ∃ bits : Nat → Bool,
      RolePrediary (finiteDummyTailCarrier H n bits) ∧
      FiniteDummyTailEventFreeTest H n bits n := by
  rintro ⟨bits,PT,hFree⟩
  exact (finiteDummyTail_fullDiary_no_fullFrameEventFree
    DH hn bits PT) hFree

/-- Positive FINITE witness of the unavoidable old-cut failure:
there exists a true nonmarker m<n where either a non-two-split
has a selected pair germ or an old leaf has a selected one-germ.
The witness is computed from finite old/tail representative
germ Finsets, NOT from an unspecified infinite tail position. -/
theorem finiteDummyTail_fullDiary_exists_finiteGermObstruction
    {H : Ordered3Graph Nat} {n : Nat}
    (DH : FiniteRoleDiaryBlock H n)
    (hn : 4 ≤ n)
    (bits : Nat → Bool)
    (PT : RolePrediary (finiteDummyTailCarrier H n bits)) :
    ∃ m : Nat, 3 ≤ m ∧ m < n ∧
      ((¬ IsTwoSplit H m ∧
          0 < (finiteDummyTailSelectedTwoGerms H n bits m).card) ∨
       (IsLeaf H m ∧
          0 < (finiteDummyTailSelectedOneGerms H n bits m).card)) := by
  classical
  by_contra hNoWitness
  have hFinite : FiniteDummyTailEventFreeTest H n bits n := by
    intro m hm3 hmn
    constructor
    · intro hNotTwo
      by_contra hNotZero
      have hPos :
          0 < (finiteDummyTailSelectedTwoGerms H n bits m).card := by
        omega
      exact hNoWitness
        ⟨m,hm3,hmn,Or.inl ⟨hNotTwo,hPos⟩⟩
    · intro hLeaf
      by_contra hNotZero
      have hPos :
          0 < (finiteDummyTailSelectedOneGerms H n bits m).card := by
        omega
      exact hNoWitness
        ⟨m,hm3,hmn,Or.inr ⟨hLeaf,hPos⟩⟩
  exact (finiteDummyTail_fullDiary_no_fullFrameEventFree
    DH hn bits PT) hFinite

/-- A genuine finite full diary DOES admit a causal global
dummy-tail RolePrediary extension, but ANY such resulting
orientation must have a concrete finite old-cut germ obstruction
to complete-prefix one-pass fixation. -/
theorem finiteDummyTail_fullDiary_exists_valid_bits_with_obstruction
    {H : Ordered3Graph Nat} {n : Nat}
    (DH : FiniteRoleDiaryBlock H n)
    (hn : 4 ≤ n) :
    ∃ bits : Nat → Bool,
      RolePrediary (finiteDummyTailCarrier H n bits) ∧
      (∃ m : Nat, 3 ≤ m ∧ m < n ∧
        ((¬ IsTwoSplit H m ∧
            0 < (finiteDummyTailSelectedTwoGerms H n bits m).card) ∨
         (IsLeaf H m ∧
            0 < (finiteDummyTailSelectedOneGerms H n bits m).card))) := by
  obtain ⟨bits,PT⟩ :=
    exists_finiteDummyTailCarrier_prediary DH.prediary
  exact ⟨bits,PT,
    finiteDummyTail_fullDiary_exists_finiteGermObstruction
      DH hn bits PT⟩

end DiaryLeafPriority
end ThreeUniformDiaries
