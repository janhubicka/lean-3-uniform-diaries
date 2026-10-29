import ThreeUniformDiaries.DiaryFiniteCanonicalFirstDifference
import ThreeUniformDiaries.DiaryFiniteFlipCrossCopyPairSeparation
import ThreeUniformDiaries.DiaryFiniteExplicitFeedbackLiteralSeparation

/-!
# Uniform feedback separation from first genuine source S2 divergence

The canonical source flip orbit is constrained, not a free Boolean
cube. Distinct actual flips first differ either in the one global
Devlin sign or at a genuine S2 witness bit.

In the global-sign case the same source reference ordered leaf pair
has opposite Devlin marker-one incidences in the two selected
bounded target copies. Every target flip globally preserves or
reverses these incidences and cannot remove the disagreement.

In the S2 case we assume the crucial GEOMETRIC fact: the TWO copies
of the same selected S2 witness leaf pair have their full pair-type
meet at the common image of the source two-split. Such a genuine
two-split full meet forces opposite E3 bits in EVERY target flip.
The explicit source triple (s,a_s,b_s) therefore separates the two
pullback codes, without using arbitrary Classical.choose maps.

The theorem is conditional ONLY on the cross-copy geometric meet
property. The actual sign-rooted construction is intended to
discharge that premise, using the verified causal and completion
meet transport.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- If the explicit bounded source-copy family has exactly the
shared S2 cross-copy meet required by the sign-rooted geometry,
then EVERY genuine target flip distinguishes every two different
canonical source flips on one literal increasing source triple.
No independent Boolean coordinates are postulated. -/
theorem finiteCanonical_explicit_maps_literal_separate_of_crossMeets
    {A B : Ordered3Graph Nat} {n k : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (maps : FiniteCanonicalFlipIndex A n → Nat → Nat)
    (hMaps : ∀ i : FiniteCanonicalFlipIndex A n,
      FiniteBoundedMeetEmbedding
        ((finiteCanonicalSignRootedFamily DA).graph i) B n k (maps i))
    (hCross : ∀ (i j : FiniteCanonicalFlipIndex A n)
      (s : FiniteTwoSplitIndex A n),
      (finiteCanonicalSignRootedFamily DA).node i s.val.val =
        (finiteCanonicalSignRootedFamily DA).node j s.val.val →
      ((finiteCanonicalSignRootedFamily DA).signature i).2 s ≠
        ((finiteCanonicalSignRootedFamily DA).signature j).2 s →
      let W := finiteSelectedS2Witness DA s
      maps i s.val.val = maps j s.val.val ∧
      B.twoMeetLevel
        (maps i W.a) (maps i W.b)
        (maps j W.a) (maps j W.b) = maps i s.val.val) :
    ∀ (T : Ordered3Graph Nat) (FT : FiniteDiaryFlip B T k)
      (i j : FiniteCanonicalFlipIndex A n),
      i ≠ j →
      ∃ a b c : Fin n, a < b ∧ b < c ∧
        ¬ (T.edge (maps i a.val) (maps i b.val) (maps i c.val) ↔
           T.edge (maps j a.val) (maps j b.val) (maps j c.val)) := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  intro T FT i j hij
  rcases finiteCanonicalSignRooted_first_difference DA i j hij with
      hSign | ⟨s, _hSameSign, hDiff, _hBefore, hShared⟩
  · have hPair : FiniteSourceHasLeafPair A n := by
      by_contra hNone
      have hGraph : F.graph i = F.graph j :=
        finite_two_flips_eq_of_no_source_leaf_pair
          DA (F.flip i) (F.flip j) hNone
      apply hij
      apply Subtype.ext
      exact finiteCanonicalSourceFlipCodes_decode_injective
        A n i.val j.val i.property j.property hGraph
    let r := (finiteSourceLeafReference A n).1
    let t := (finiteSourceLeafReference A n).2
    obtain ⟨hrt,htn,hr,ht⟩ :=
      finiteSourceLeafReference_spec A n hPair
    have hrn : r < n := by omega
    have hOneR : 1 < r := by have h := hr.1; omega
    have hSourceDec :
        decide ((F.graph i).edge 1 r t) ≠
        decide ((F.graph j).edge 1 r t) := by
      change decide ((F.graph i).edge 1 r t) ≠
        decide ((F.graph j).edge 1 r t) at hSign
      exact hSign
    have hSourceDifferent :
        ¬ ((F.graph i).edge 1 r t ↔ (F.graph j).edge 1 r t) := by
      by_cases hi : (F.graph i).edge 1 r t <;>
        by_cases hj : (F.graph j).edge 1 r t <;>
        simp_all
    have hEdgeI :
        B.edge 1 (maps i r) (maps i t) ↔
          (F.graph i).edge 1 r t := by
      have he := (hMaps i).toMeetEmbedding.edge_iff
        1 r t hOneR hrt htn
      simpa only [(hMaps i).toMeetEmbedding.marker_one] using he
    have hEdgeJ :
        B.edge 1 (maps j r) (maps j t) ↔
          (F.graph j).edge 1 r t := by
      have he := (hMaps j).toMeetEmbedding.edge_iff
        1 r t hOneR hrt htn
      simpa only [(hMaps j).toMeetEmbedding.marker_one] using he
    have hDifferentB :
        ¬ (B.edge 1 (maps i r) (maps i t) ↔
           B.edge 1 (maps j r) (maps j t)) := by
      intro hSame
      exact hSourceDifferent (hEdgeI.symm.trans (hSame.trans hEdgeJ))
    have hLeafI_r : IsLeaf (F.graph i) r :=
      ((F.flip i).role_iff r hr.1 hrn).1.mp hr
    have hLeafI_t : IsLeaf (F.graph i) t :=
      ((F.flip i).role_iff t ht.1 htn).1.mp ht
    have hLeafJ_r : IsLeaf (F.graph j) r :=
      ((F.flip j).role_iff r hr.1 hrn).1.mp hr
    have hLeafJ_t : IsLeaf (F.graph j) t :=
      ((F.flip j).role_iff t ht.1 htn).1.mp ht
    have hLeafB_ir : IsLeaf B (maps i r) :=
      ((hMaps i).toMeetEmbedding.leaf_iff r hr.1 hrn).mpr hLeafI_r
    have hLeafB_it : IsLeaf B (maps i t) :=
      ((hMaps i).toMeetEmbedding.leaf_iff t ht.1 htn).mpr hLeafI_t
    have hLeafB_jr : IsLeaf B (maps j r) :=
      ((hMaps j).toMeetEmbedding.leaf_iff r hr.1 hrn).mpr hLeafJ_r
    have hLeafB_jt : IsLeaf B (maps j t) :=
      ((hMaps j).toMeetEmbedding.leaf_iff t ht.1 htn).mpr hLeafJ_t
    have hDifferentT :=
      finite_flip_preserves_markerOne_pair_disagreement
        FT (maps i r) (maps i t) (maps j r) (maps j t)
        ((hMaps i).toMeetEmbedding.strictMono hrt)
        ((hMaps j).toMeetEmbedding.strictMono hrt)
        ((hMaps i).image_bound t htn)
        ((hMaps j).image_bound t htn)
        hLeafB_ir hLeafB_it hLeafB_jr hLeafB_jt hDifferentB
    refine ⟨⟨1,by omega⟩,⟨r,hrn⟩,⟨t,htn⟩,
      hOneR,hrt,?_⟩
    simpa only [(hMaps i).toMeetEmbedding.marker_one,
      (hMaps j).toMeetEmbedding.marker_one] using hDifferentT
  · let W := finiteSelectedS2Witness DA s
    have han : W.a < n := lt_trans W.hab W.hbn
    obtain ⟨hSharedImage,hCrossMeet⟩ :=
      hCross i j s hShared hDiff
    have hTwoSource : IsTwoSplit (F.graph i) s.val.val :=
      ((F.flip i).role_iff s.val.val s.property.1 s.val.isLt).2.2.mp
        s.property
    have hTwoB : IsTwoSplit B (maps i s.val.val) :=
      ((hMaps i).toMeetEmbedding.twoSplit_iff
        s.val.val s.property.1 s.val.isLt).mpr hTwoSource
    have hLeafI_a : IsLeaf (F.graph i) W.a :=
      ((F.flip i).role_iff W.a W.ha.1 han).1.mp W.ha
    have hLeafI_b : IsLeaf (F.graph i) W.b :=
      ((F.flip i).role_iff W.b W.hb.1 W.hbn).1.mp W.hb
    have hLeafJ_a : IsLeaf (F.graph j) W.a :=
      ((F.flip j).role_iff W.a W.ha.1 han).1.mp W.ha
    have hLeafJ_b : IsLeaf (F.graph j) W.b :=
      ((F.flip j).role_iff W.b W.hb.1 W.hbn).1.mp W.hb
    have hLeafB_ia : IsLeaf B (maps i W.a) :=
      ((hMaps i).toMeetEmbedding.leaf_iff W.a W.ha.1 han).mpr hLeafI_a
    have hLeafB_ib : IsLeaf B (maps i W.b) :=
      ((hMaps i).toMeetEmbedding.leaf_iff W.b W.hb.1 W.hbn).mpr hLeafI_b
    have hLeafB_ja : IsLeaf B (maps j W.a) :=
      ((hMaps j).toMeetEmbedding.leaf_iff W.a W.ha.1 han).mpr hLeafJ_a
    have hLeafB_jb : IsLeaf B (maps j W.b) :=
      ((hMaps j).toMeetEmbedding.leaf_iff W.b W.hb.1 W.hbn).mpr hLeafJ_b
    have hSplitBeforeJ : maps i s.val.val < maps j W.a := by
      rw [hSharedImage]
      exact (hMaps j).toMeetEmbedding.strictMono W.hsa
    have hDifferentT :=
      finite_flip_preserves_twoSplit_pair_disagreement
        FT (maps i s.val.val)
        (maps i W.a) (maps i W.b)
        (maps j W.a) (maps j W.b)
        hTwoB
        ((hMaps i).toMeetEmbedding.strictMono W.hab)
        ((hMaps j).toMeetEmbedding.strictMono W.hab)
        ((hMaps i).image_bound W.b W.hbn)
        ((hMaps j).image_bound W.b W.hbn)
        hLeafB_ia hLeafB_ib hLeafB_ja hLeafB_jb
        ((hMaps i).toMeetEmbedding.strictMono W.hsa)
        hSplitBeforeJ hCrossMeet
    refine ⟨⟨s.val.val,s.val.isLt⟩,⟨W.a,han⟩,
      ⟨W.b,W.hbn⟩,W.hsa,W.hab,?_⟩
    simpa only [← hSharedImage] using hDifferentT

end DiaryLeafPriority
end ThreeUniformDiaries
