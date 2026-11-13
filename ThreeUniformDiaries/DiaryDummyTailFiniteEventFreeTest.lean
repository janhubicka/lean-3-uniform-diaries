import ThreeUniformDiaries.DiaryDummyTailGermExplicitFiniteSets
import ThreeUniformDiaries.DiaryOnePassSelectedGermProtectedCut
import ThreeUniformDiaries.DiaryFiniteDummyTailRoleCoherence

/-!
# Track B: event-free old prefix is exactly a finite old/tail germ test

The full old-cut realised singleton and pair-germ sets of an actual
countable dummy-tail carrier are equal to EXPLICIT finite Finsets.
The concrete one-pass schedule chooses one default germ from each
old parent fibre and inserts an event for every OTHER realised
child. We substitute the exact finite census into these genuine
default and selected-germ definitions.

Consequently, for p<=n, absence of all actual one-pass event blocks
below the protected cut p is equivalent to a finite collection of
zero-cardinality tests on the finite source diagram H, its genuine
old roles and the finite cross-orientation bits. There is NO hidden
quantification over arbitrary late dummy-tail vertices or pairs:
the finite census has already exhausted all such realisations.

This is a formal reduction to a finite compatibility problem.
It emphatically does NOT prove that compatible cross bits exist
for a given finite source, nor that those bits also support the
required full V/E prediary and strong every-target-flip absorber.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Default singleton successor chosen from the explicitly finite
old/tail census rather than existentially over the countable tail. -/
noncomputable def finiteDummyTailOneDefaultGerm
    (H : Ordered3Graph Nat) (n : Nat) (bits : Nat → Bool)
    (m : Nat) (parent : OneCodeSpace m) :
    Option (OneGermSpace m) := by
  classical
  let T := finiteDummyTailCarrier H n bits
  let R := finiteDummyTailOneGermCensus H n bits m
  let F := R.filter (fun g => g.1 = parent)
  exact if oneGermCode T m m ∈ F then
    some (oneGermCode T m m)
  else leastOneGermByRank m F.toList

/-- Default pair germ chosen from the finite representative census. -/
noncomputable def finiteDummyTailTwoDefaultGerm
    (H : Ordered3Graph Nat) (n : Nat) (bits : Nat → Bool)
    (m : Nat) (parent : TwoCodeSpace m) :
    Option (TwoGermSpace m) := by
  classical
  let R := finiteDummyTailTwoGermCensus H n bits m
  exact (R.filter (fun g => g.1 = parent)).toList.head?

/-- The actual finite singleton-event classes obtained by
filtering the explicit old/tail census against its finite defaults. -/
noncomputable def finiteDummyTailSelectedOneGerms
    (H : Ordered3Graph Nat) (n : Nat) (bits : Nat → Bool)
    (m : Nat) : Finset (OneGermSpace m) := by
  classical
  let R := finiteDummyTailOneGermCensus H n bits m
  exact R.filter (fun g =>
    some g ≠ finiteDummyTailOneDefaultGerm H n bits m g.1)

/-- The actual finite pair-event classes obtained from the
complete finite representative census. -/
noncomputable def finiteDummyTailSelectedTwoGerms
    (H : Ordered3Graph Nat) (n : Nat) (bits : Nat → Bool)
    (m : Nat) : Finset (TwoGermSpace m) := by
  classical
  let R := finiteDummyTailTwoGermCensus H n bits m
  exact R.filter (fun g =>
    some g ≠ finiteDummyTailTwoDefaultGerm H n bits m g.1)

/-- At old m<n, the DEFAULT singleton germ used by the verified
one-pass algorithm is LITERALLY the default computed from the
finite source/tail representative census. -/
theorem finiteDummyTail_oneDefaultGerm_eq_finite
    (H : Ordered3Graph Nat) (n : Nat)
    (FH : FiniteDiaryEdgeFrame H n) (bits : Nat → Bool)
    (m : Nat) (hm : m < n) (parent : OneCodeSpace m) :
    oneDefaultGerm (finiteDummyTailCarrier H n bits) m parent =
      finiteDummyTailOneDefaultGerm H n bits m parent := by
  classical
  let T := finiteDummyTailCarrier H n bits
  have hR : realisedOneGerms T m =
      finiteDummyTailOneGermCensus H n bits m :=
    finiteDummyTail_realisedOneGerms_eq_finiteCensus
      H n FH bits m hm
  change
    (if oneGermCode T m m ∈
        (realisedOneGerms T m).filter (fun g => g.1 = parent)
      then some (oneGermCode T m m)
      else leastOneGermByRank m
        ((realisedOneGerms T m).filter
          (fun g => g.1 = parent)).toList) =
    (if oneGermCode T m m ∈
        (finiteDummyTailOneGermCensus H n bits m).filter
          (fun g => g.1 = parent)
      then some (oneGermCode T m m)
      else leastOneGermByRank m
        ((finiteDummyTailOneGermCensus H n bits m).filter
          (fun g => g.1 = parent)).toList)
  rw [hR]

/-- At old m<n, the ACTUAL default pair germ is exactly the
default read from the finite representative census. -/
theorem finiteDummyTail_twoDefaultGerm_eq_finite
    (H : Ordered3Graph Nat) (n : Nat)
    (FH : FiniteDiaryEdgeFrame H n) (bits : Nat → Bool)
    (m : Nat) (hm : m < n) (parent : TwoCodeSpace m) :
    twoDefaultGerm (finiteDummyTailCarrier H n bits) m parent =
      finiteDummyTailTwoDefaultGerm H n bits m parent := by
  classical
  let T := finiteDummyTailCarrier H n bits
  have hR : realisedTwoGerms T m =
      finiteDummyTailTwoGermCensus H n bits m :=
    finiteDummyTail_realisedTwoGerms_eq_finiteCensus
      H n FH bits m hm
  change
    ((realisedTwoGerms T m).filter
      (fun g => g.1 = parent)).toList.head? =
    ((finiteDummyTailTwoGermCensus H n bits m).filter
      (fun g => g.1 = parent)).toList.head?
  rw [hR]

/-- Exact identification of the true selected singleton-event
Finset of the infinite countable dummy-tail carrier with its
explicit FINITE old/tail representative computation. -/
theorem finiteDummyTail_selectedOneGerms_eq_finite
    (H : Ordered3Graph Nat) (n : Nat)
    (FH : FiniteDiaryEdgeFrame H n) (bits : Nat → Bool)
    (m : Nat) (hm : m < n) :
    selectedOneGerms (finiteDummyTailCarrier H n bits) m =
      finiteDummyTailSelectedOneGerms H n bits m := by
  classical
  let T := finiteDummyTailCarrier H n bits
  have hR : realisedOneGerms T m =
      finiteDummyTailOneGermCensus H n bits m :=
    finiteDummyTail_realisedOneGerms_eq_finiteCensus
      H n FH bits m hm
  apply Finset.ext
  intro g
  change
    g ∈ (realisedOneGerms T m).filter
      (fun h => some h ≠ oneDefaultGerm T m h.1) ↔
    g ∈ (finiteDummyTailOneGermCensus H n bits m).filter
      (fun h => some h ≠ finiteDummyTailOneDefaultGerm H n bits m h.1)
  simp only [Finset.mem_filter, hR,
    finiteDummyTail_oneDefaultGerm_eq_finite H n FH bits m hm]

/-- Exact identification of the true selected pair-event Finset
with its explicit finite old/tail representative computation. -/
theorem finiteDummyTail_selectedTwoGerms_eq_finite
    (H : Ordered3Graph Nat) (n : Nat)
    (FH : FiniteDiaryEdgeFrame H n) (bits : Nat → Bool)
    (m : Nat) (hm : m < n) :
    selectedTwoGerms (finiteDummyTailCarrier H n bits) m =
      finiteDummyTailSelectedTwoGerms H n bits m := by
  classical
  let T := finiteDummyTailCarrier H n bits
  have hR : realisedTwoGerms T m =
      finiteDummyTailTwoGermCensus H n bits m :=
    finiteDummyTail_realisedTwoGerms_eq_finiteCensus
      H n FH bits m hm
  apply Finset.ext
  intro g
  change
    g ∈ (realisedTwoGerms T m).filter
      (fun h => some h ≠ twoDefaultGerm T m h.1) ↔
    g ∈ (finiteDummyTailTwoGermCensus H n bits m).filter
      (fun h => some h ≠ finiteDummyTailTwoDefaultGerm H n bits m h.1)
  simp only [Finset.mem_filter, hR,
    finiteDummyTail_twoDefaultGerm_eq_finite H n FH bits m hm]

/-- An EXPLICIT finite compatibility test for no selected
one-pass events below a protected old cut p<=n.
The role conditions refer to the genuine FINITE source graph H,
not an unverified infinite-tail role predicate. -/
def FiniteDummyTailEventFreeTest
    (H : Ordered3Graph Nat) (n : Nat) (bits : Nat → Bool)
    (p : Nat) : Prop :=
  ∀ m : Nat, 3 ≤ m → m < p →
    (¬ IsTwoSplit H m →
      (finiteDummyTailSelectedTwoGerms H n bits m).card = 0) ∧
    (IsLeaf H m →
      (finiteDummyTailSelectedOneGerms H n bits m).card = 0)

/-- The actual infinite dummy-tail one-pass schedule is
event-free below p exactly when the FINITE source/cross-bit
test succeeds. This is a finite decision reduction, NOT
the existence of a satisfying cross orientation. -/
theorem finiteDummyTail_noEventsBelow_iff_finiteTest
    (H : Ordered3Graph Nat) (n : Nat)
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (p : Nat) (hp : p ≤ n) :
    OnePassNoEventsBelow (finiteDummyTailCarrier H n bits) p ↔
      FiniteDummyTailEventFreeTest H n bits p := by
  let T := finiteDummyTailCarrier H n bits
  rw [onePassNoEventsBelow_iff_noSelectedGerms T p]
  constructor
  · intro h m hm3 hmp
    have hm : m < n := by omega
    have hTwo := finiteDummyTailCarrier_old_twoSplit_iff
      FH bits m hm
    have hLeaf := finiteDummyTailCarrier_old_leaf_iff
      FH bits m hm
    have hLocal := h m hm3 hmp
    constructor
    · intro hnTwo
      have ht : ¬ IsTwoSplit T m := by
        intro htm
        exact hnTwo (hTwo.mp htm)
      have hs := hLocal.1 ht
      rw [finiteDummyTail_selectedTwoGerms_eq_finite
        H n FH bits m hm] at hs
      exact hs
    · intro hl
      have ht : IsLeaf T m := hLeaf.mpr hl
      have hs := hLocal.2 ht
      rw [finiteDummyTail_selectedOneGerms_eq_finite
        H n FH bits m hm] at hs
      exact hs
  · intro h m hm3 hmp
    have hm : m < n := by omega
    have hTwo := finiteDummyTailCarrier_old_twoSplit_iff
      FH bits m hm
    have hLeaf := finiteDummyTailCarrier_old_leaf_iff
      FH bits m hm
    have hLocal := h m hm3 hmp
    constructor
    · intro hnTwoT
      have hnTwoH : ¬ IsTwoSplit H m := by
        intro ht
        exact hnTwoT (hTwo.mpr ht)
      have hs := hLocal.1 hnTwoH
      rw [← finiteDummyTail_selectedTwoGerms_eq_finite
        H n FH bits m hm] at hs
      exact hs
    · intro hlT
      have hlH : IsLeaf H m := hLeaf.mp hlT
      have hs := hLocal.2 hlH
      rw [← finiteDummyTail_selectedOneGerms_eq_finite
        H n FH bits m hm] at hs
      exact hs

end DiaryLeafPriority
end ThreeUniformDiaries
