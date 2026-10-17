import ThreeUniformDiaries.DiaryOnePassFreshOneMeet
import ThreeUniformDiaries.DiaryOnePassFreshWitnessCones
import ThreeUniformDiaries.DiaryOnePassOldSplitWitnessTransport

/-!
# Full V1 witness axiom for the actual one-pass target

The previous checked local theorem proves the meet EXACTLY at a
fresh singleton event, given a positive selected source germ and
a negative realised default sibling in the same parent.

Such genuine source leaves exist at EVERY selected event: the
source event label is an actual selected germ, and the default
child theorem produces a different realised sibling. The source
leaves embed as actual target leaves after the new event, and
their singleton meet is numerically the event vertex.

The source V1 witness is already transported exactly at every
OLD split image. Exhausting all actual target event positions
therefore proves the literal RolePrediary.one_split_witness field
of the concrete one-pass target for ALL original and fresh 1-splits.

This uses only the source V/E pre-diary, not S1/S2 or an assumed
target diary. V2 fresh witnesses, V3 and S1/S2 remain open.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- Every actual NEW singleton event has source leaf witnesses
whose target one-meet is EXACTLY this event vertex. -/
theorem onePassRawTarget_freshOne_has_witness
    (P : RolePrediary H) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : OneGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.singleton m g) :
    ∃ a b : Nat,
      IsLeaf (onePassRawTarget H) a ∧
      IsLeaf (onePassRawTarget H) b ∧
      onePassEventPosition H m i < a ∧
      onePassEventPosition H m i < b ∧
      (onePassRawTarget H).oneMeetLevel a b =
        onePassEventPosition H m i := by
  have hg : g ∈ selectedOneGerms H m :=
    onePassEventAt_singleton_selected H m i g hget
  obtain ⟨h,hReal,hParent,hneq,hDefault⟩ :=
    selectedOneGerm_has_distinct_default H m g hg
  obtain ⟨u,hu,hmu,hug⟩ :=
    selectedOneGerm_source_leaf H m g hg
  obtain ⟨v,hv,hmv,hvh⟩ :=
    realisedOneGerm_source_leaf H m h hReal
  have hMeet :=
    onePass_freshOne_selected_default_meet_exact P m
      i g h hget hDefault hParent u v hu hv hmu hmv
      hug hvh hneq
  exact ⟨onePassOldImage H u, onePassOldImage H v,
    (onePassRawTarget_old_leaf_iff H u).mpr hu,
    (onePassRawTarget_old_leaf_iff H v).mpr hv,
    onePassEventPosition_lt_oldImage H m u i hmu,
    onePassEventPosition_lt_oldImage H m v i hmv,
    hMeet⟩

/-- COMPLETE literal V1 witness field on the real target:
EVERY original or inserted 1-split has later target leaf
witnesses whose singleton meet is exactly the split level. -/
theorem onePassRawTarget_one_split_witness
    (P : RolePrediary H) :
    ∀ e : Nat, IsOneSplit (onePassRawTarget H) e →
      ∃ a b : Nat,
        IsLeaf (onePassRawTarget H) a ∧
        IsLeaf (onePassRawTarget H) b ∧
        e < a ∧ e < b ∧
        (onePassRawTarget H).oneMeetLevel a b = e := by
  intro e he
  rcases onePass_target_index_covered H e with
      ⟨m,hm⟩ | ⟨m,i,hm⟩
  · subst e
    exact onePass_oldOneSplit_has_witness P m
      ((onePassRawTarget_old_oneSplit_iff H m).mp he)
  · subst e
    rcases onePass_event_label_at_own_cut H m i with
        ⟨g,hPair⟩ | ⟨g,hOne⟩
    · have hTwo := onePassRawTarget_fresh_twoSplit
        H m i g hPair
      exact False.elim (hTwo.2.1 he.2.1)
    · exact onePassRawTarget_freshOne_has_witness
        P m i g hOne

end DiaryLeafPriority
end ThreeUniformDiaries
