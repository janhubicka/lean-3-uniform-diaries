import ThreeUniformDiaries.DiaryOnePassEventReflection

/-!
# Exact role-marker classification at inserted one-pass event vertices

Both role markers for a fresh event are computed from the actual
target hypergraph, not assigned independently by a unary role tag.

The raw construction puts marker (0,1,e) on singleton events and
(0,2,e) on pair events. The hard direction is EXCLUSION: another
copied or inserted edge may not supply the opposite marker. This
follows from fresh-event support, increasing index bounds and
globally unique event positions.

Hence every inserted singleton event satisfies the literal target
IsOneSplit predicate, and every inserted pair event satisfies
IsTwoSplit. This closes the fresh-event role-disjointness part of E.
It does not assert V1/V2 coherence/witnesses, all target vertices'
roles, complete V3 or S1/S2.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The (0,1,e) target marker at a fresh event exists if and only
if the event really is a singleton-germ event. -/
theorem onePassRawTarget_marker_one_event_iff
    (H : Ordered3Graph Nat) (m : Nat)
    (i : Fin (onePassBlock H m).length) :
    (onePassRawTarget H).edge 0 1 (onePassEventPosition H m i) ↔
      ∃ g : OneGermSpace m,
        onePassEventAt H m i = BlockEvent.singleton m g := by
  constructor
  · intro he
    rcases he with hOld | hNew
    · obtain ⟨a,b,c,habc,hx,hy,hz⟩ := hOld
      exact False.elim
        ((onePassEventPosition_ne_oldImage H m i c) hz)
    · obtain ⟨n,j,_,hOne|hTwo⟩ := hNew
      · obtain ⟨g,hget,hMarker|hInc⟩ := hOne
        · obtain ⟨hx,hy,hz⟩ := hMarker
          have hnm : n = m :=
            onePassEventPosition_eq_cut H n m j i hz.symm
          subst n
          have hji : j = i :=
            onePassEventPosition_injective_same_cut H m j i hz.symm
          subst j
          exact ⟨g,hget⟩
        · obtain ⟨u,hu,hnu,hcode,hx,hy,hz⟩ := hInc
          have hge := onePassEventPosition_ge_three H n j
          omega
      · obtain ⟨g,hget,hMarker|hInc⟩ := hTwo
        · obtain ⟨hx,hy,hz⟩ := hMarker
          omega
        · obtain ⟨u,v,hu,hv,hnu,huv,hcode,hx,hy,hz⟩ := hInc
          have hge := onePassEventPosition_ge_three H n j
          omega
  · rintro ⟨g,hget⟩
    exact onePassRawTarget_singleton_marker H m i g hget

/-- The (0,2,e) marker at a fresh event exists if and only if
the event really is a full-pair-germ event. -/
theorem onePassRawTarget_marker_two_event_iff
    (H : Ordered3Graph Nat) (m : Nat)
    (i : Fin (onePassBlock H m).length) :
    (onePassRawTarget H).edge 0 2 (onePassEventPosition H m i) ↔
      ∃ g : TwoGermSpace m,
        onePassEventAt H m i = BlockEvent.pair m g := by
  constructor
  · intro he
    rcases he with hOld | hNew
    · obtain ⟨a,b,c,habc,hx,hy,hz⟩ := hOld
      exact False.elim
        ((onePassEventPosition_ne_oldImage H m i c) hz)
    · obtain ⟨n,j,_,hOne|hTwo⟩ := hNew
      · obtain ⟨g,hget,hMarker|hInc⟩ := hOne
        · obtain ⟨hx,hy,hz⟩ := hMarker
          omega
        · obtain ⟨u,hu,hnu,hcode,hx,hy,hz⟩ := hInc
          have hge := onePassEventPosition_ge_three H n j
          omega
      · obtain ⟨g,hget,hMarker|hInc⟩ := hTwo
        · obtain ⟨hx,hy,hz⟩ := hMarker
          have hnm : n = m :=
            onePassEventPosition_eq_cut H n m j i hz.symm
          subst n
          have hji : j = i :=
            onePassEventPosition_injective_same_cut H m j i hz.symm
          subst j
          exact ⟨g,hget⟩
        · obtain ⟨u,v,hu,hv,hnu,huv,hcode,hx,hy,hz⟩ := hInc
          have hge := onePassEventPosition_ge_three H n j
          omega
  · rintro ⟨g,hget⟩
    exact onePassRawTarget_pair_marker H m i g hget

/-- Literal target 1-split role of every fresh singleton event,
including the NEGATION of the other role marker. -/
theorem onePassRawTarget_fresh_oneSplit
    (H : Ordered3Graph Nat) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : OneGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.singleton m g) :
    IsOneSplit (onePassRawTarget H) (onePassEventPosition H m i) := by
  refine ⟨onePassEventPosition_ge_three H m i,
    onePassRawTarget_singleton_marker H m i g hget, ?_⟩
  intro he
  obtain ⟨g',hget'⟩ := (onePassRawTarget_marker_two_event_iff H m i).mp he
  have hbad : BlockEvent.singleton m g = BlockEvent.pair m g' :=
    hget.symm.trans hget'
  cases hbad

/-- Literal target 2-split role of every fresh pair event,
including the NEGATION of the other role marker. -/
theorem onePassRawTarget_fresh_twoSplit
    (H : Ordered3Graph Nat) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : TwoGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.pair m g) :
    IsTwoSplit (onePassRawTarget H) (onePassEventPosition H m i) := by
  refine ⟨onePassEventPosition_ge_three H m i, ?_,
    onePassRawTarget_pair_marker H m i g hget⟩
  intro he
  obtain ⟨g',hget'⟩ := (onePassRawTarget_marker_one_event_iff H m i).mp he
  have hbad : BlockEvent.pair m g = BlockEvent.singleton m g' :=
    hget.symm.trans hget'
  cases hbad

end DiaryLeafPriority
end ThreeUniformDiaries
