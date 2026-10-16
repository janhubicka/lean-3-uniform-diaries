import ThreeUniformDiaries.DiaryOnePassTargetLeafCones
import ThreeUniformDiaries.DiaryOnePassGlobalOneTypeTransport
import ThreeUniformDiaries.DiaryOnePassNonLeafSingletonBlocks
import ThreeUniformDiaries.DiaryOnePassBlockGermTransport

/-!
# V1 coherence for the actual one-pass target

Positive singleton events in the raw target are actual source
normal/terminal germ classes. Global singleton source-cut transport
gives target equality at the start of B_m; the checked block
refinement then gives target equality through the whole block.
In particular positive leaves agree at the earlier fresh split.

At the image of an ORIGINAL 1-split the argument is instead the
source V1 coherence together with copied zero-marker incidences,
global singleton transport before B_m, and the fact that an
original nonleaf block inserts no singleton type tests.

Exhaust the ACTUAL target's split vertices using the certified
old-or-event enumeration. This proves the genuine V1 coherence
field for ALL 1-splits and ALL positive target leaves, not merely
an abstract finite-code interface.

V1 witnesses, V2/V3, S1/S2 and flip absorption remain separate.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- Each actual fresh singleton event in B_m can occur only when
the original source vertex m is a LEAF. -/
theorem onePass_freshOne_event_source_leaf
    (H : Ordered3Graph Nat) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : OneGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.singleton m g) :
    IsLeaf H m := by
  by_contra hNotLeaf
  exact (onePassBlock_no_singleton_event_of_not_leaf
    H m hNotLeaf i g) hget

/-- Genuine coherence below the position of a new 1-split:
every two target leaves positive at that event agree as ACTUAL
target singleton types below the event's natural-number level. -/
theorem onePassRawTarget_freshOne_coherent
    (P : RolePrediary H) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : OneGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.singleton m g)
    (a b : Nat)
    (ha : IsLeaf (onePassRawTarget H) a)
    (hb : IsLeaf (onePassRawTarget H) b)
    (hea : (onePassRawTarget H).edge 0
      (onePassEventPosition H m i) a)
    (heb : (onePassRawTarget H).edge 0
      (onePassEventPosition H m i) b) :
    (onePassRawTarget H).SameOneTypeBelow
      (onePassEventPosition H m i) a b := by
  obtain ⟨u, hu, hmu, hgu, hua⟩ :=
    (onePassRawTarget_freshOne_positive_leaf_iff
      H m a i g hget).mp ⟨ha, hea⟩
  obtain ⟨v, hv, hmv, hgv, hvb⟩ :=
    (onePassRawTarget_freshOne_positive_leaf_iff
      H m b i g hget).mp ⟨hb, heb⟩
  subst a
  subst b
  have hLeaf : IsLeaf H m :=
    onePass_freshOne_event_source_leaf H m i g hget
  have hParentCode : oneCode H m u = oneCode H m v := by
    have hgerm : oneGermCode H m u = oneGermCode H m v :=
      hgu.trans hgv.symm
    exact congrArg Prod.fst hgerm
  have hParent : H.SameOneTypeBelow m u v :=
    (oneCode_eq_iff_sameOneType H m u v).mp hParentCode
  have hm3 : 3 ≤ m := hLeaf.1
  have hBegin :
      (onePassRawTarget H).SameOneTypeBelow
        (onePassBefore H m)
        (onePassOldImage H u) (onePassOldImage H v) :=
    (onePass_global_oneType_transport P m u v
      hm3 hu hv hmu hmv).mp hParent
  have hFull :
      (onePassRawTarget H).SameOneTypeBelow
        (onePassOldImage H m)
        (onePassOldImage H u) (onePassOldImage H v) :=
    (onePassBlock_oneType_refinement_iff P m u v
      hLeaf hu hv hmu hmv hParentCode).mpr
      ⟨hBegin,hgu.trans hgv.symm⟩
  have hBefore :
      onePassEventPosition H m i < onePassOldImage H m :=
    (onePassEventPosition_interval H m i).2
  intro x y hxy hy
  exact hFull hxy (by omega)

/-- At any ORIGINAL source 1-split, the raw target's V1
coherence is inherited through exact zero-marker edge reflection
and the global original-cut singleton-type theorem. -/
theorem onePassRawTarget_oldOne_coherent
    (P : RolePrediary H) (m : Nat)
    (hm : IsOneSplit (onePassRawTarget H) (onePassOldImage H m))
    (a b : Nat)
    (ha : IsLeaf (onePassRawTarget H) a)
    (hb : IsLeaf (onePassRawTarget H) b)
    (hea : (onePassRawTarget H).edge 0
       (onePassOldImage H m) a)
    (heb : (onePassRawTarget H).edge 0
       (onePassOldImage H m) b) :
    (onePassRawTarget H).SameOneTypeBelow
       (onePassOldImage H m) a b := by
  obtain ⟨u,hu,hua⟩ :=
    (onePassRawTarget_leaf_iff_oldLeaf_image H a).mp ha
  obtain ⟨v,hv,hvb⟩ :=
    (onePassRawTarget_leaf_iff_oldLeaf_image H b).mp hb
  subst a
  subst b
  have hmSource : IsOneSplit H m :=
    (onePassRawTarget_old_oneSplit_iff H m).mp hm
  have heU : H.edge 0 m u := by
    apply (onePassRawTarget_edge_image_iff H 0 m u).mp
    simpa only [onePassOldImage_zero] using hea
  have heV : H.edge 0 m v := by
    apply (onePassRawTarget_edge_image_iff H 0 m v).mp
    simpa only [onePassOldImage_zero] using heb
  have hmu : m ≤ u := by
    have h := (P.edge_ordered 0 m u heU).2
    omega
  have hmv : m ≤ v := by
    have h := (P.edge_ordered 0 m v heV).2
    omega
  have hParent : H.SameOneTypeBelow m u v :=
    P.one_split_coherent m u v hmSource hu hv heU heV
  have hBegin :
      (onePassRawTarget H).SameOneTypeBelow
        (onePassBefore H m)
        (onePassOldImage H u) (onePassOldImage H v) :=
    (onePass_global_oneType_transport P m u v
      hmSource.1 hu hv hmu hmv).mp hParent
  have hNotLeaf : ¬ IsLeaf H m := by
    intro h
    exact h.2.1 hmSource.2.1
  exact (onePassBlock_oneType_unchanged_of_not_leaf
    P m (onePassOldImage H u) (onePassOldImage H v)
    hNotLeaf).mpr hBegin

/-- The complete V1 COHERENCE clause of the proposed one-pass
raw target, covering both original and freshly inserted 1-splits,
all actual target leaves, and their actual marker-0 incidences. -/
theorem onePassRawTarget_one_split_coherent
    (P : RolePrediary H) :
    ∀ m a b,
      IsOneSplit (onePassRawTarget H) m →
      IsLeaf (onePassRawTarget H) a →
      IsLeaf (onePassRawTarget H) b →
      (onePassRawTarget H).edge 0 m a →
      (onePassRawTarget H).edge 0 m b →
      (onePassRawTarget H).SameOneTypeBelow m a b := by
  intro e a b he ha hb hea heb
  rcases onePass_target_index_covered H e with
      ⟨m,hm⟩ | ⟨m,i,hm⟩
  · subst e
    exact onePassRawTarget_oldOne_coherent
      P m he a b ha hb hea heb
  · subst e
    rcases onePass_event_label_at_own_cut H m i with
        ⟨g,hPair⟩ | ⟨g,hOne⟩
    · have hTwo := onePassRawTarget_fresh_twoSplit H m i g hPair
      exact False.elim (hTwo.2.1 he.2.1)
    · exact onePassRawTarget_freshOne_coherent
        P m i g hOne a b ha hb hea heb

end DiaryLeafPriority
end ThreeUniformDiaries
