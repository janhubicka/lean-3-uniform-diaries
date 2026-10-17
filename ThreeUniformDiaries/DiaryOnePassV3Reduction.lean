import ThreeUniformDiaries.DiaryOnePassTargetLeafCones
import ThreeUniformDiaries.DiaryPrediaryDefinition

/-!
# Reduce the actual target V3 field to old source leaf order

The one-pass construction introduces NO new leaves. The full target
leaf set is precisely the image of the source leaf set, with its
original order preserved. All Devlin marker edges (1,a,b)/(2,a,b)
on original ordered leaf pairs are copied INDUCEDLY from the source.

Consequently the COMPLETE pair of target V3 marker equivalences
is true if and only if the one-pass embedding preserves the
manuscript's LexEarlier relation on ordered original source leaves.

This is an exact, two-way reduction for the actual target graph;
it does not postulate a V3 clause. The remaining proof obligation
is now ONE precise numerical-order statement for the source pair
of leaves, using the corrected finite-block lex scheduling and
global singleton-type transport.

No S1/S2, target pre-diary, or artificial lex relation is assumed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Exact preservation of the manuscript's source lexicographic
comparison between old leaves by the actual one-pass embedding. -/
def OnePassPreservesSourceLex (H : Ordered3Graph Nat) : Prop :=
  ∀ a b : Nat, a < b → IsLeaf H a → IsLeaf H b →
    (LexEarlier (onePassRawTarget H)
       (onePassOldImage H a) (onePassOldImage H b) ↔
     LexEarlier H a b)

/-- The complete V3 marker clauses on all actual target leaves. -/
def OnePassTargetV3 (H : Ordered3Graph Nat) : Prop :=
  (∀ a b : Nat, a < b →
    IsLeaf (onePassRawTarget H) a →
    IsLeaf (onePassRawTarget H) b →
    ((onePassRawTarget H).edge 1 a b ↔
     LexEarlier (onePassRawTarget H) a b)) ∧
  (∀ a b : Nat, a < b →
    IsLeaf (onePassRawTarget H) a →
    IsLeaf (onePassRawTarget H) b →
    ((onePassRawTarget H).edge 2 a b ↔
     ¬ LexEarlier (onePassRawTarget H) a b))

/-- The one-pass source embedding preserves all Devlin marker
edges at ordered old leaf pairs, at BOTH marker coordinates. -/
theorem onePass_oldDevlinMarkers_reflect
    (H : Ordered3Graph Nat) (a b : Nat) :
    ((onePassRawTarget H).edge 1
      (onePassOldImage H a) (onePassOldImage H b) ↔
       H.edge 1 a b) ∧
    ((onePassRawTarget H).edge 2
      (onePassOldImage H a) (onePassOldImage H b) ↔
       H.edge 2 a b) := by
  constructor
  · simpa only [onePassOldImage_one] using
      (onePassRawTarget_edge_image_iff H 1 a b)
  · simpa only [onePassOldImage_two] using
      (onePassRawTarget_edge_image_iff H 2 a b)

/-- V3 in the actual target is equivalent to preservation of
the old leaf lex comparison. All leaves are old images and
the target contains precisely the copied old Devlin marker
edges, so no other V3 case remains to be checked. -/
theorem onePassTargetV3_iff_sourceLex
    {H : Ordered3Graph Nat} (P : RolePrediary H) :
    OnePassTargetV3 H ↔ OnePassPreservesSourceLex H := by
  constructor
  · rintro ⟨hOne,_hTwo⟩ a b hab ha hb
    have hTargetA : IsLeaf (onePassRawTarget H)
        (onePassOldImage H a) :=
      (onePassRawTarget_old_leaf_iff H a).mpr ha
    have hTargetB : IsLeaf (onePassRawTarget H)
        (onePassOldImage H b) :=
      (onePassRawTarget_old_leaf_iff H b).mpr hb
    have hOrder :
        onePassOldImage H a < onePassOldImage H b :=
      (onePassOldImage_strictMono H) hab
    have hMarker :=
      (onePass_oldDevlinMarkers_reflect H a b).1
    exact (hOne _ _ hOrder hTargetA hTargetB).symm.trans
      (hMarker.trans (P.leaf_marker_one a b hab ha hb))
  · intro hLex
    constructor
    · intro a b hab ha hb
      obtain ⟨u,hu,hua⟩ :=
        (onePassRawTarget_leaf_iff_oldLeaf_image H a).mp ha
      obtain ⟨v,hv,hvb⟩ :=
        (onePassRawTarget_leaf_iff_oldLeaf_image H b).mp hb
      subst a
      subst b
      have huv : u < v := by
        by_contra hNot
        have hvu : v ≤ u := by omega
        have hMon := (onePassOldImage_strictMono H).monotone hvu
        omega
      exact ((onePass_oldDevlinMarkers_reflect H u v).1).trans
        ((P.leaf_marker_one u v huv hu hv).trans
         (hLex u v huv hu hv).symm)
    · intro a b hab ha hb
      obtain ⟨u,hu,hua⟩ :=
        (onePassRawTarget_leaf_iff_oldLeaf_image H a).mp ha
      obtain ⟨v,hv,hvb⟩ :=
        (onePassRawTarget_leaf_iff_oldLeaf_image H b).mp hb
      subst a
      subst b
      have huv : u < v := by
        by_contra hNot
        have hvu : v ≤ u := by omega
        have hMon := (onePassOldImage_strictMono H).monotone hvu
        omega
      exact ((onePass_oldDevlinMarkers_reflect H u v).2).trans
        ((P.leaf_marker_two u v huv hu hv).trans
         (not_congr (hLex u v huv hu hv).symm))

end DiaryLeafPriority
end ThreeUniformDiaries
