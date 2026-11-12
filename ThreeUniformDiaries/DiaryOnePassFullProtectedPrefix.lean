import ThreeUniformDiaries.DiaryOnePassProtectedPrefixEventCriterion
import ThreeUniformDiaries.DiaryOnePassCompleteS2
import ThreeUniformDiaries.DiaryLiteralOldPrefixFullPairMeets

/-!
# Track B: event-free one-pass completion is a full diary with a literal prefix

The verified one-pass theorem turns any countable RolePrediary H into
a genuine countable RoleDiary K. Its original vertices are typically
moved by inserted events, so no literal old numerical prefix is
automatically preserved.

If the concrete event schedule has NO selected event blocks below a
chosen numerical cut p, the prior exact event criterion makes the old
image the literal identity on [0,p). Old induced edges and nonedges
agree there. The source/target edge-order axioms also show that ALL
raw triples with third coordinate <p agree (not only increasing
triples), giving exact marker roles, ALL capped numerical singleton
meets and ALL capped full ordered-pair meets on the prefix.

This is a conditional relative COMPLETE diary theorem: the still
missing mathematical construction must supply a prediary with the
required prescribed prefix and event-free schedule. It is NOT
a literal proper extension theorem for an old full FINITE diary.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- With a genuine RolePrediary input, no one-pass events below p
ensures full raw old-prefix agreement (including non-increasing
triples), not just the original induced-copy iff at shifted ranks. -/
theorem onePass_noEvents_literalOldPrefix
    {H : Ordered3Graph Nat} (P : RolePrediary H)
    (p : Nat) (hNo : OnePassNoEventsBelow H p) :
    LiteralOldPrefixAgreement H (onePassRawTarget H) p := by
  intro a b c hc
  by_cases hord : a < b ∧ b < c
  · have ha : a < p := by omega
    have hb : b < p := by omega
    exact (onePassRawTarget_edge_iff_on_noEvent_prefix
      H p hNo a b c ha hb hc).symm
  · have hSource : ¬ H.edge a b c := by
      intro he
      exact hord (P.edge_ordered a b c he)
    have hTarget : ¬ (onePassRawTarget H).edge a b c := by
      intro he
      exact hord ((onePassRawTarget_isDiary P).edge_ordered a b c he)
    exact iff_of_false hSource hTarget

/-- The ACTUAL one-pass countable full RoleDiary completion
retains a prescribed OLD numerical prefix literally on every
edge, nonedge, marker-defined role, capped singleton meet, and
full ordered-pair meet, provided the prediary has no event blocks
below that protected cut.

The only premises are a supplied genuine RolePrediary and the
explicit finite-cut event schedule condition. No relative
existence claim is made. -/
theorem onePass_fullDiary_and_exactProtectedPrefix
    {H : Ordered3Graph Nat} (P : RolePrediary H)
    (p : Nat) (hNo : OnePassNoEventsBelow H p) :
    let K := onePassRawTarget H
    RoleDiary K ∧
    LiteralOldPrefixAgreement H K p ∧
    (∀ u : Nat, u < p →
      (IsLeaf H u ↔ IsLeaf K u) ∧
      (IsOneSplit H u ↔ IsOneSplit K u) ∧
      (IsTwoSplit H u ↔ IsTwoSplit K u)) ∧
    (∀ u v : Nat, u < p → v < p →
      H.oneMeetLevel u v = K.oneMeetLevel u v) ∧
    (∀ a b c d : Nat, a < p → b < p → c < p → d < p →
      H.twoMeetLevel a b c d = K.twoMeetLevel a b c d) := by
  dsimp only
  have hPrefix := onePass_noEvents_literalOldPrefix P p hNo
  refine ⟨onePassRawTarget_isDiary P,hPrefix,?_,?_,?_⟩
  · intro u hu
    exact role_iff_of_literalOldPrefix hPrefix u hu
  · intro u v hu hv
    exact oneMeetLevel_eq_of_literalOldPrefix hPrefix u v hu hv
  · intro a b c d ha hb hc hd
    exact twoMeetLevel_eq_of_literalOldPrefix
      hPrefix a b c d ha hb hc hd

end DiaryLeafPriority
end ThreeUniformDiaries
