import ThreeUniformDiaries.DiaryOnePassFreshTwoMeet
import ThreeUniformDiaries.DiaryOnePassFreshWitnessCones
import ThreeUniformDiaries.DiaryOnePassOldSplitWitnessTransport

/-!
# Full V2 witness axiom in the actual one-pass target

Every original 2-split keeps its exact source pair-meet witnesses.
Every fresh 2-split is an indexed selected full pair germ g. Its
same-parent default h is realised and distinct. Actual source leaf
pairs witnessing g,h embed as ordered target leaf pairs strictly
above the event, and their full target pair meet is exactly the
fresh split event's Nat level.

Exhausting all target vertices as old levels or fresh events proves
the full RolePrediary.two_split_witness field for the candidate.
This uses source V/E alone, with no postulated target diary.
V3, S1/S2, protected meets, and flip absorption remain separate.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- Every fresh selected pair-germ event has two later actual target
ordered leaf pairs whose full two-type meet equals this event. -/
theorem onePassRawTarget_freshTwo_has_witness
    (P : RolePrediary H) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : TwoGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.pair m g) :
    ∃ a b c d : Nat,
      a < b ∧ c < d ∧
      IsLeaf (onePassRawTarget H) a ∧
      IsLeaf (onePassRawTarget H) b ∧
      IsLeaf (onePassRawTarget H) c ∧
      IsLeaf (onePassRawTarget H) d ∧
      onePassEventPosition H m i < a ∧
      onePassEventPosition H m i < c ∧
      (onePassRawTarget H).twoMeetLevel a b c d =
        onePassEventPosition H m i := by
  have hg : g ∈ selectedTwoGerms H m :=
    onePassEventAt_pair_selected H m i g hget
  obtain ⟨h,hReal,hParent,hneq,hDefault⟩ :=
    selectedTwoGerm_has_distinct_default H m g hg
  obtain ⟨u,v,hu,hv,hmu,huv,huvg⟩ :=
    selectedTwoGerm_source_pair H m g hg
  obtain ⟨a,b,ha,hb,hma,hab,habh⟩ :=
    realisedTwoGerm_source_pair H m h hReal
  have hMeet :=
    onePass_freshTwo_selected_default_meet_exact P m
      i g h hget hDefault hParent u v a b
      hu hv ha hb hmu hma huv hab huvg habh hneq
  refine ⟨onePassOldImage H u, onePassOldImage H v,
    onePassOldImage H a, onePassOldImage H b,
    (onePassOldImage_strictMono H) huv,
    (onePassOldImage_strictMono H) hab,
    (onePassRawTarget_old_leaf_iff H u).mpr hu,
    (onePassRawTarget_old_leaf_iff H v).mpr hv,
    (onePassRawTarget_old_leaf_iff H a).mpr ha,
    (onePassRawTarget_old_leaf_iff H b).mpr hb,
    onePassEventPosition_lt_oldImage H m u i hmu,
    onePassEventPosition_lt_oldImage H m a i hma,
    hMeet⟩

/-- COMPLETE literal V2 witness field on the actual one-pass
target: every original or inserted 2-split has later ordered
target leaf pairs whose full pair-type meet is exactly that
split's target level. -/
theorem onePassRawTarget_two_split_witness
    (P : RolePrediary H) :
    ∀ e : Nat, IsTwoSplit (onePassRawTarget H) e →
      ∃ a b c d : Nat, a < b ∧ c < d ∧
        IsLeaf (onePassRawTarget H) a ∧
        IsLeaf (onePassRawTarget H) b ∧
        IsLeaf (onePassRawTarget H) c ∧
        IsLeaf (onePassRawTarget H) d ∧
        e < a ∧ e < c ∧
        (onePassRawTarget H).twoMeetLevel a b c d = e := by
  intro e he
  rcases onePass_target_index_covered H e with
      ⟨m,hm⟩ | ⟨m,i,hm⟩
  · subst e
    exact onePass_oldTwoSplit_has_witness P m
      ((onePassRawTarget_old_twoSplit_iff H m).mp he)
  · subst e
    rcases onePass_event_label_at_own_cut H m i with
        ⟨g,hPair⟩ | ⟨g,hOne⟩
    · exact onePassRawTarget_freshTwo_has_witness P m i g hPair
    · have hOneSplit :=
        onePassRawTarget_fresh_oneSplit H m i g hOne
      exact False.elim (he.2.1 hOneSplit.2.1)

end DiaryLeafPriority
end ThreeUniformDiaries
