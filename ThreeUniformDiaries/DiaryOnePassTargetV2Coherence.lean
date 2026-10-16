import ThreeUniformDiaries.DiaryOnePassTargetLeafCones
import ThreeUniformDiaries.DiaryOnePassFreshTwoCoherence
import ThreeUniformDiaries.DiaryOnePassGlobalTwoTypeTransport

/-!
# V2 coherence of every actual 2-split in the one-pass target

All target leaves are images of original source leaves. At an old
2-split, exact edge reflection carries positive pairs back to the
source. Source V2 coherence and global full two-type transport give
agreement at B_m; this block is empty at an old 2-split. At a fresh
pair event, the already checked actual old-image coherence applies
to all target leaf pairs.

This proves the complete V2 coherence field but not V2 witnesses,
V3, S1/S2 or flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- V2 coherence at the image of every original 2-split. -/
theorem onePassRawTarget_oldTwo_coherent
    (P : RolePrediary H) (m a b c d : Nat)
    (hm : IsTwoSplit (onePassRawTarget H) (onePassOldImage H m))
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf (onePassRawTarget H) a)
    (hb : IsLeaf (onePassRawTarget H) b)
    (hc : IsLeaf (onePassRawTarget H) c)
    (hd : IsLeaf (onePassRawTarget H) d)
    (hAB : (onePassRawTarget H).edge
      (onePassOldImage H m) a b)
    (hCD : (onePassRawTarget H).edge
      (onePassOldImage H m) c d) :
    (onePassRawTarget H).SameTwoTypeBelow
      (onePassOldImage H m) a b c d := by
  obtain ⟨u,hu,hua⟩ :=
    (onePassRawTarget_leaf_iff_oldLeaf_image H a).mp ha
  obtain ⟨v,hv,hvb⟩ :=
    (onePassRawTarget_leaf_iff_oldLeaf_image H b).mp hb
  obtain ⟨s,hs,hsc⟩ :=
    (onePassRawTarget_leaf_iff_oldLeaf_image H c).mp hc
  obtain ⟨t,ht,htd⟩ :=
    (onePassRawTarget_leaf_iff_oldLeaf_image H d).mp hd
  subst a
  subst b
  subst c
  subst d
  have hmSource : IsTwoSplit H m :=
    (onePassRawTarget_old_twoSplit_iff H m).mp hm
  have heUV : H.edge m u v :=
    (onePassRawTarget_edge_image_iff H m u v).mp hAB
  have heST : H.edge m s t :=
    (onePassRawTarget_edge_image_iff H m s t).mp hCD
  have hOrderUV := P.edge_ordered m u v heUV
  have hOrderST := P.edge_ordered m s t heST
  have hSource : H.SameTwoTypeBelow m u v s t :=
    P.two_split_coherent m u v s t hmSource
      hOrderUV.2 hOrderST.2 hu hv hs ht heUV heST
  have hTarget :
      (onePassRawTarget H).SameTwoTypeBelow
        (onePassBefore H m)
        (onePassOldImage H u) (onePassOldImage H v)
        (onePassOldImage H s) (onePassOldImage H t) :=
    (onePass_global_twoType_transport P m u v s t
      hmSource.1 hu hv hs ht
      hOrderUV.2 hOrderST.2
      hOrderUV.1.le hOrderST.1.le).mp hSource
  have hNotLeaf : ¬ IsLeaf H m := by
    intro hLeaf
    exact hLeaf.2.2 hmSource.2.2
  have hSmall : ¬ m < 3 := by
    have h3 := hmSource.1
    omega
  have hEmpty : onePassBlock H m = [] := by
    simp [onePassBlock, hSmall, hmSource, hNotLeaf]
  have hCut : onePassBefore H m = onePassOldImage H m := by
    simp [onePassOldImage, onePassBlockSize, hEmpty]
  simpa only [hCut] using hTarget

/-- Fresh 2-split coherence for all target ordered leaf pairs. -/
theorem onePassRawTarget_freshTwo_coherent
    (P : RolePrediary H) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : TwoGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.pair m g)
    (a b c d : Nat)
    (ha : IsLeaf (onePassRawTarget H) a)
    (hb : IsLeaf (onePassRawTarget H) b)
    (hc : IsLeaf (onePassRawTarget H) c)
    (hd : IsLeaf (onePassRawTarget H) d)
    (hAB : (onePassRawTarget H).edge
       (onePassEventPosition H m i) a b)
    (hCD : (onePassRawTarget H).edge
       (onePassEventPosition H m i) c d) :
    (onePassRawTarget H).SameTwoTypeBelow
       (onePassEventPosition H m i) a b c d := by
  obtain ⟨u,hu,hua⟩ :=
    (onePassRawTarget_leaf_iff_oldLeaf_image H a).mp ha
  obtain ⟨v,hv,hvb⟩ :=
    (onePassRawTarget_leaf_iff_oldLeaf_image H b).mp hb
  obtain ⟨s,hs,hsc⟩ :=
    (onePassRawTarget_leaf_iff_oldLeaf_image H c).mp hc
  obtain ⟨t,ht,htd⟩ :=
    (onePassRawTarget_leaf_iff_oldLeaf_image H d).mp hd
  subst a
  subst b
  subst c
  subst d
  have hSourceUV :=
    (onePassRawTarget_pair_incidence_iff
      H m u v i g hget).mp hAB
  have hSourceST :=
    (onePassRawTarget_pair_incidence_iff
      H m s t i g hget).mp hCD
  exact onePassRawTarget_freshTwo_coherent_oldImages
    P m i g hget u v s t hu hv hs ht
    hSourceUV.2.2.2.1 hSourceST.2.2.2.1 hAB hCD

/-- Complete V2 positive-pair coherence in the concrete target. -/
theorem onePassRawTarget_two_split_coherent
    (P : RolePrediary H) :
    ∀ m a b c d,
      IsTwoSplit (onePassRawTarget H) m →
      a < b → c < d →
      IsLeaf (onePassRawTarget H) a →
      IsLeaf (onePassRawTarget H) b →
      IsLeaf (onePassRawTarget H) c →
      IsLeaf (onePassRawTarget H) d →
      (onePassRawTarget H).edge m a b →
      (onePassRawTarget H).edge m c d →
      (onePassRawTarget H).SameTwoTypeBelow m a b c d := by
  intro e a b c d he hab hcd ha hb hc hd hAB hCD
  rcases onePass_target_index_covered H e with
      ⟨m,hm⟩ | ⟨m,i,hm⟩
  · subst e
    exact onePassRawTarget_oldTwo_coherent
      P m a b c d he hab hcd ha hb hc hd hAB hCD
  · subst e
    rcases onePass_event_label_at_own_cut H m i with
        ⟨g,hPair⟩ | ⟨g,hOne⟩
    · exact onePassRawTarget_freshTwo_coherent
        P m i g hPair a b c d ha hb hc hd hAB hCD
    · have hOneSplit :=
        onePassRawTarget_fresh_oneSplit H m i g hOne
      exact False.elim (he.2.1 hOneSplit.2.1)

end DiaryLeafPriority
end ThreeUniformDiaries
