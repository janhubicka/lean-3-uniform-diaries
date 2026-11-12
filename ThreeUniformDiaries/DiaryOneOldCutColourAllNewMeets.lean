import ThreeUniformDiaries.DiaryTailFullPairMeetCone
import ThreeUniformDiaries.DiaryFiniteSingletonColour

/-!
# Track C: ONE complete old-cut singleton colour fixes all new S1/S2 meets

English proof and adversarial audit:
  janhubicka/3-uniform-diaries PR #311

For ANY target ordered 3-graph K, full singleton-colour equality
at a finite target cut B yields SameOneTypeBelow B. The already
verified exact S1 and full-S2 second-tail invariance theorems then
fix all three numerical new-leaf generator shapes over fixed old
vertices before B:
  1. old/new singleton meet;
  2. old-old versus old-new full pair meet;
  3. old-new versus old-new full pair meet.

No target RoleDiary axioms, genericity, finite Ramsey, candidate
generator-table functionality, or new-leaf persistence is needed.
For old roots W all below B and new candidates beyond W, this
controls ALL numerical S1/S2 values with one selected new leaf.

It does NOT assert that these values equal SOURCE-required numeric
generators, that a finite candidate table is functional, that
the candidate has the right roles and E2/E3 edges, or that any
candidate survives all future diary horizons.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Equality of ONE complete mixed singleton colour at the old cut B
forces EXACT equality of every numerical meet shape involving one
candidate new vertex, with old first coordinates a,c strictly below B.

For the S1 component both new values lie AFTER the old root a.
For the cross S2 component the fixed second coordinate b contributes
a reflexive singleton type. For the new-new S2 component BOTH second
coordinates change from v to w and use the SAME colour equality.

No full-diary or target-role assumptions are required. -/
theorem same_complete_singletonColour_fixes_all_oneNew_meets
    (K : Ordered3Graph Nat) (B a b c v w : Nat)
    (haB : a < B) (hcB : c < B)
    (hav : a < v) (haw : a < w)
    (hColour :
      DiaryLowerBoundColors.singletonColour K B v =
        DiaryLowerBoundColors.singletonColour K B w) :
    K.oneMeetLevel a v = K.oneMeetLevel a w ∧
    K.twoMeetLevel a b c v = K.twoMeetLevel a b c w ∧
    K.twoMeetLevel a v c v = K.twoMeetLevel a w c w := by
  have hSame : K.SameOneTypeBelow B v w :=
    (DiaryLowerBoundColors.singletonColour_eq_iff K B v w).mp hColour
  have hReflexive : K.SameOneTypeBelow B b b := by
    intro x y hxy hy
    exact Iff.rfl
  refine ⟨?_, ?_, ?_⟩
  · exact oneMeetLevel_eq_of_sameOneTypeBelow_cut
      K B a v w haB hav haw hSame
  · exact twoMeetLevel_eq_of_second_tail_types
      K B a c b b v w haB hcB hReflexive hSame
  · exact twoMeetLevel_eq_of_second_tail_types
      K B a c v w v w haB hcB hSame hSame

/-- Finite-root simultaneous version: if all old selected target
vertices lie strictly below B, and both genuine proposed later
vertices v,w lie after each old root, the ONE full singleton
B-colour equality determines ALL old/new S1 values and BOTH
families of full S2 numerical meets with an old root as first
coordinate. This includes old-old/new and old-new/new pairs.

The induced mixed E2/E3 edge table, generator-functionality,
source-required values, and actual future-horizon persistence
are separate checks; this is precisely a NUMERIC invariance lemma. -/
theorem same_complete_singletonColour_fixes_finiteRoot_newMeets
    (K : Ordered3Graph Nat) (B : Nat) (W : Finset Nat)
    (v w : Nat)
    (hRootsBelow : ∀ a : Nat, a ∈ W → a < B)
    (hCandidatesAfter : ∀ a : Nat, a ∈ W → a < v ∧ a < w)
    (hColour :
      DiaryLowerBoundColors.singletonColour K B v =
        DiaryLowerBoundColors.singletonColour K B w) :
    (∀ a : Nat, a ∈ W →
      K.oneMeetLevel a v = K.oneMeetLevel a w) ∧
    (∀ a b c : Nat, a ∈ W → b ∈ W → c ∈ W →
      K.twoMeetLevel a b c v = K.twoMeetLevel a b c w) ∧
    (∀ a c : Nat, a ∈ W → c ∈ W →
      K.twoMeetLevel a v c v = K.twoMeetLevel a w c w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    exact (same_complete_singletonColour_fixes_all_oneNew_meets
      K B a a a v w
      (hRootsBelow a ha) (hRootsBelow a ha)
      (hCandidatesAfter a ha).1 (hCandidatesAfter a ha).2
      hColour).1
  · intro a b c ha hb hc
    exact (same_complete_singletonColour_fixes_all_oneNew_meets
      K B a b c v w
      (hRootsBelow a ha) (hRootsBelow c hc)
      (hCandidatesAfter a ha).1 (hCandidatesAfter a ha).2
      hColour).2.1
  · intro a c ha hc
    exact (same_complete_singletonColour_fixes_all_oneNew_meets
      K B a a c v w
      (hRootsBelow a ha) (hRootsBelow c hc)
      (hCandidatesAfter a ha).1 (hCandidatesAfter a ha).2
      hColour).2.2

end DiaryLeafPriority
end ThreeUniformDiaries
