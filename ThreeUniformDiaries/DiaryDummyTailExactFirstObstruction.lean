import ThreeUniformDiaries.DiaryDummyTailFullFrameEventFreeObstruction
import Mathlib.Data.Nat.Find
import Lean.Elab.Tactic.Omega

/-!
# Track B: exact first-obstruction cutoff for a valid full finite dummy tail

The merged finite selected-germ census gives an exact test for a fixed
old cut. The merged full-frame obstruction says that every valid dummy
tail of a complete finite diary fails this test somewhere below n.

For a FIXED globally valid dummy-tail orientation, take the LEAST
failing old nonmarker level p. Then the finite event-free test holds
for a cut q precisely when q <= p (including arbitrary q, not just
q <= n). At p itself the already verified one-pass/compression route
gives a genuine finite full diary with literally protected raw
edge/nonedge, role and exact capped meet data.

This is an exact *boundary certificate*, not a proof of a large
protected cut or a relative strong absorber. The cut can be as small
as marker cutoff 3, depends on the actual chosen bits, and the
extracted finite target has no asserted every-flip absorption or
recursive reserve/capture invariant.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For a globally valid dummy-tail prediary of a full finite diary,
there is a first old nonmarker selected-germ obstruction p<n.
The finite event-free compatibility test succeeds at exactly the cuts
q<=p. It yields a genuine finite full diary retaining the whole
literal prefix below p and its exact capped singleton and full pair meets.

No existence of a larger protected proper prefix, no recursive
protected absorber, no selected bounded-rank tower, and no coherent
countable-source flip absorption is inferred. -/
theorem finiteDummyTail_fullDiary_exact_firstBadCut_and_completion
    {H : Ordered3Graph Nat} {n : Nat}
    (DH : FiniteRoleDiaryBlock H n)
    (hn : 4 ≤ n)
    (bits : Nat → Bool)
    (PT : RolePrediary (finiteDummyTailCarrier H n bits)) :
    ∃ p : Nat,
      3 ≤ p ∧ p < n ∧
      (∀ q : Nat,
        FiniteDummyTailEventFreeTest H n bits q ↔ q ≤ p) ∧
      (∃ (C : Ordered3Graph Nat) (m : Nat),
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
        (IsLeaf C (m-1) ∧ p ≤ m-1)) := by
  classical
  let Bad : Nat → Prop := fun m =>
    3 ≤ m ∧ m < n ∧
      ((¬ IsTwoSplit H m ∧
          0 < (finiteDummyTailSelectedTwoGerms H n bits m).card) ∨
       (IsLeaf H m ∧
          0 < (finiteDummyTailSelectedOneGerms H n bits m).card))
  have hExists : ∃ m, Bad m :=
    finiteDummyTail_fullDiary_exists_finiteGermObstruction DH hn bits PT
  let p : Nat := Nat.find hExists
  have hp : Bad p := Nat.find_spec hExists
  have hNoEarlier : ∀ m : Nat, m < p → ¬ Bad m := by
    intro m hm
    exact Nat.find_min hExists hm
  have hExact :
      ∀ q : Nat,
        FiniteDummyTailEventFreeTest H n bits q ↔ q ≤ p := by
    intro q
    constructor
    · intro hTest
      by_contra hNotLe
      have hpq : p < q := by omega
      have hAtP := hTest p hp.1 hpq
      rcases hp.2.2 with hTwo | hOne
      · have hZero := hAtP.1 hTwo.1
        omega
      · have hZero := hAtP.2 hOne.1
        omega
    · intro hq
      intro m hm3 hmq
      have hmp : m < p := by omega
      have hmn : m < n := by omega
      have hNotBad : ¬ Bad m := hNoEarlier m hmp
      constructor
      · intro hNotTwo
        by_contra hNotZero
        have hPositive :
            0 < (finiteDummyTailSelectedTwoGerms H n bits m).card := by
          omega
        apply hNotBad
        exact ⟨hm3, hmn, Or.inl ⟨hNotTwo, hPositive⟩⟩
      · intro hLeaf
        by_contra hNotZero
        have hPositive :
            0 < (finiteDummyTailSelectedOneGerms H n bits m).card := by
          omega
        apply hNotBad
        exact ⟨hm3, hmn, Or.inr ⟨hLeaf, hPositive⟩⟩
  have hpLe : p ≤ n := by omega
  have hFinite : FiniteDummyTailEventFreeTest H n bits p :=
    (hExact p).2 (le_refl p)
  have hCompletion :=
    finiteDummyTail_finiteTest_yields_fullFiniteRelativeCompletion
      DH.prediary bits PT p hpLe hFinite
  exact ⟨p, hp.1, hp.2.1, hExact, hCompletion⟩

end DiaryLeafPriority
end ThreeUniformDiaries
