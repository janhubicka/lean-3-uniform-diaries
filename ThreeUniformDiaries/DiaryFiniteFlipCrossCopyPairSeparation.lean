import ThreeUniformDiaries.DiaryFiniteGlobalDevlinOrientation
import ThreeUniformDiaries.DiaryFiniteLeafMeetTwoSplitDisagreement
import ThreeUniformDiaries.DiaryFiniteFlipTransitivity

/-!
# Two uniform separation witnesses under every finite diary flip

For target-flip absorption we must compare the SAME two actual
target leaf pairs in two potentially distinct embedded copies.
The source indices or the source flip codes may differ, so the
existing SAME-source witness rigidity theorem does not directly
apply.

Two robust distinctions do survive ANY genuine flip of a target:
(1) unequal marker-one bits on two ordered target leaf pairs
remain unequal, since a finite flip preserves or simultaneously
reverses every Devlin orientation bit;
(2) if the full pair-type meet of two target leaf pairs is a
genuine target 2-split, the two E3 incidences at that split
remain unequal, since full numerical leaf-pair meets and
genuine split roles are flip-invariant, and E1--E5 forbid
singleton predecessor tests with middle coordinate a 2-split.

These are unconditional mathematical separation principles;
they do not assert that a suitable pair of leaf-pair images
has the required full meet in a proposed finite absorber.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Any difference in Devlin marker-one orientation on two
genuine bounded ordered leaf pairs survives every genuine
target flip, even when the two pairs come from distinct
source branches. The sign may reverse, but only globally. -/
theorem finite_flip_preserves_markerOne_pair_disagreement
    {B T : Ordered3Graph Nat} {k : Nat}
    (F : FiniteDiaryFlip B T k)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (hbn : b < k) (hdn : d < k)
    (ha : IsLeaf B a) (hb : IsLeaf B b)
    (hc : IsLeaf B c) (hd : IsLeaf B d)
    (hDiff : ¬ (B.edge 1 a b ↔ B.edge 1 c d)) :
    ¬ (T.edge 1 a b ↔ T.edge 1 c d) := by
  rcases finite_flip_marker_one_global_sign F with hPres | hRev
  · have hAB := hPres a b hab hbn ha hb
    have hCD := hPres c d hcd hdn hc hd
    tauto
  · have hAB := hRev a b hab hbn ha hb
    have hCD := hRev c d hcd hdn hc hd
    tauto

/-- When two ordered leaf pairs have full pair-type meet at an
actual source 2-split, EVERY genuine target flip must assign
OPPOSITE E3 bits to them at that same split. This is stronger
than comparing the bits of two separate flips on one pair:
it compares two DIFFERENT target pairs at the same time. -/
theorem finite_flip_preserves_twoSplit_pair_disagreement
    {B T : Ordered3Graph Nat} {k : Nat}
    (F : FiniteDiaryFlip B T k)
    (s a b c d : Nat)
    (hs : IsTwoSplit B s)
    (hab : a < b) (hcd : c < d)
    (hbn : b < k) (hdn : d < k)
    (ha : IsLeaf B a) (hb : IsLeaf B b)
    (hc : IsLeaf B c) (hd : IsLeaf B d)
    (hsa : s < a) (hsc : s < c)
    (hMeet : B.twoMeetLevel a b c d = s) :
    ¬ (T.edge s a b ↔ T.edge s c d) := by
  have hsn : s < k := F.source_diary.prediary.twoSplit_lt s hs
  have hsT : IsTwoSplit T s :=
    ((F.role_iff s hs.1 hsn).2.2).mp hs
  have hMeetT : T.twoMeetLevel a b c d = s :=
    (F.leaf_twoMeet a b c d hab hcd hbn hdn ha hb hc hd).symm.trans hMeet
  exact E_twoSplit_pair_aux_distinguishes
    F.target_diary.prediary.permitted_edge
    s a b c d hsT hsa hsc hMeetT

end DiaryLeafPriority
end ThreeUniformDiaries
