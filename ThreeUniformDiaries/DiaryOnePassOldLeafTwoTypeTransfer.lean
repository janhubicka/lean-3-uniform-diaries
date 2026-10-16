import ThreeUniformDiaries.DiaryOnePassLeafBlockTwoTypeTransport
import ThreeUniformDiaries.DiaryOnePassOldLeafColumnStability

/-!
# Full pair-type transport through the image of an original leaf

After the finite event block B_m, the ORIGINAL source leaf m is
copied to its target vertex f(m). It can create singleton column
tests (z,f(m),f(u)) from old copied edges or from earlier pair
events, and auxiliary tests (f(m),f(a),f(b)) from copied source
triple edges.

For ORIGINAL ordered source leaf pairs strictly above m, equality
of their SOURCE full pair type through cut m+1 already determines
all these new tests:
* singleton columns are constant by the verified delayed old-leaf
  column theorem (including earlier and capped pair events);
* the auxiliary first-coordinate bit is the original edge
  (m,a,b), reflected exactly by the induced old copy.

Consequently, after the verified germ-refining event block B_m,
passing f(m) adds no further distinction between source pairs
already equal at m+1. Conversely target agreement after f(m)
implies agreement before f(m) and the block-refinement theorem
recovers the source successor type.

This is the conditional ORIGINAL LEAF step for the full two-type
global induction, not an assertion of the final target diary S2.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- If source ordered leaf pairs agree in full two-type through
m+1, every newly available target test at the old leaf vertex
f(m) already agrees. -/
theorem onePass_oldLeaf_twoType_extends_of_nextSource
    (P : RolePrediary H) (m a b c d : Nat)
    (hm : IsLeaf H m)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hma : m < a) (hmc : m < c)
    (hab : a < b) (hcd : c < d)
    (hSource : H.SameTwoTypeBelow (m + 1) a b c d)
    (hBefore : (onePassRawTarget H).SameTwoTypeBelow
        (onePassOldImage H m)
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d)) :
    (onePassRawTarget H).SameTwoTypeBelow
        (onePassOldImage H m + 1)
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) := by
  have hmb : m < b := by omega
  have hmd : m < d := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy hy
    by_cases hOld : y < onePassOldImage H m
    · exact hBefore.1 hxy hOld
    · have hEq : y = onePassOldImage H m := by omega
      subst y
      exact onePass_oldLeaf_column_stable_of_nextOneType
        P m a c hm ha hc hma hmc hSource.1 x hxy
  · intro x y hxy hy
    by_cases hOld : y < onePassOldImage H m
    · exact hBefore.2.1 hxy hOld
    · have hEq : y = onePassOldImage H m := by omega
      subst y
      exact onePass_oldLeaf_column_stable_of_nextOneType
        P m b d hm hb hd hmb hmd hSource.2.1 x hxy
  · intro x hx
    by_cases hOld : x < onePassOldImage H m
    · exact hBefore.2.2 hOld
    · have hEq : x = onePassOldImage H m := by omega
      subst x
      have hEdge : H.edge m a b ↔ H.edge m c d :=
        hSource.2.2 (by omega)
      exact (onePassRawTarget_edge_image_iff H m a b).trans
        (hEdge.trans (onePassRawTarget_edge_image_iff H m c d).symm)

/-- The entire ORIGINAL LEAF step for complete ordered pair-type
transport, conditional only on the previous source/target cut
partition agreement BEFORE block B_m. -/
theorem onePass_original_leaf_twoType_transfer
    (P : RolePrediary H) (m a b c d : Nat)
    (hm : IsLeaf H m)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hma : m < a) (hmc : m < c)
    (hab : a < b) (hcd : c < d)
    (hPrevious : H.SameTwoTypeBelow m a b c d ↔
      (onePassRawTarget H).SameTwoTypeBelow
        (onePassBefore H m)
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d)) :
    H.SameTwoTypeBelow (m + 1) a b c d ↔
      (onePassRawTarget H).SameTwoTypeBelow
        (onePassOldImage H m + 1)
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) := by
  constructor
  · intro hSourceNext
    have hParent : H.SameTwoTypeBelow m a b c d := by
      refine ⟨?_, ?_, ?_⟩
      · intro x y hxy hy
        exact hSourceNext.1 hxy (by omega)
      · intro x y hxy hy
        exact hSourceNext.2.1 hxy (by omega)
      · intro x hx
        exact hSourceNext.2.2 (by omega)
    have hBlock :=
      onePass_leafBlock_twoType_refinement_iff P m a b c d hm
        hab hcd ha hb hc hd hma.le hmc.le hParent
    have hBeforeBlock :=
      hBlock.mpr ⟨hPrevious.mp hParent, hSourceNext⟩
    exact onePass_oldLeaf_twoType_extends_of_nextSource
      P m a b c d hm ha hb hc hd hma hmc hab hcd
      hSourceNext hBeforeBlock
  · intro hTargetNext
    have hTargetOld :
        (onePassRawTarget H).SameTwoTypeBelow
          (onePassOldImage H m)
          (onePassOldImage H a) (onePassOldImage H b)
          (onePassOldImage H c) (onePassOldImage H d) := by
      refine ⟨?_, ?_, ?_⟩
      · intro x y hxy hy
        exact hTargetNext.1 hxy (by omega)
      · intro x y hxy hy
        exact hTargetNext.2.1 hxy (by omega)
      · intro x hx
        exact hTargetNext.2.2 (by omega)
    have hBegin :
        (onePassRawTarget H).SameTwoTypeBelow
          (onePassBefore H m)
          (onePassOldImage H a) (onePassOldImage H b)
          (onePassOldImage H c) (onePassOldImage H d) :=
      ((onePassBlock_twoType_interval_iff H m
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d)).mp
        hTargetOld).1
    have hParent : H.SameTwoTypeBelow m a b c d :=
      hPrevious.mpr hBegin
    exact ((onePass_leafBlock_twoType_refinement_iff
      P m a b c d hm hab hcd ha hb hc hd hma.le hmc.le
      hParent).mp hTargetOld).2

end DiaryLeafPriority
end ThreeUniformDiaries
