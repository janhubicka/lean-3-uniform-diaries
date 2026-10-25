import ThreeUniformDiaries.DiaryFiniteSignRootedMarkerTypeStability
import ThreeUniformDiaries.DiaryFiniteSignRootedOrderedMarkerComparison
import ThreeUniformDiaries.DiaryFiniteSignRootedRawVOneCompatibility
import ThreeUniformDiaries.DiaryFiniteSignRootedRawVTwoCompatibility

/-!
# Conditional V1/V2 parent stability for the ORDERED marker extension

The corrected cross-marker extension includes pairs of distinct
raw leaf nodes TIED at their original source levels. A source-level-
respecting candidate ambient order agrees with the old extension on
all strictly increasing original-level terminal pairs, by the exact
marker relation comparison theorem.

Every singleton predecessor test below a shared cut s of a later
source leaf has this increasing-level property. So do all auxiliary
pair-type tests whose two terminal leaves lie on an original source
branch. Therefore a PREFIX-UNIFORM orientation preserves every
verified RAW cross-branch positive V1/V2 predecessor type after the
new order-parametrised marker extension, including all raw earlier
nodes and allowing different E3 bits at a shared two-split.

This closes the CONDITIONAL V1/V2 marker-stability calculation for
an order extending source levels. It does not construct an
orientation which is simultaneously prefix-uniform and equal to
literal LexEarlier under the final enumerated graph. That V3
existence theorem, and protected numerical mixed meets, remain open.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace FiniteSignRootedFlipFamily

variable {A : Ordered3Graph Nat} {n : Nat} {ι : Type*}

/-- Complete singleton predecessor comparison under the corrected
ordered cross-marker extension. The cut is in original source
levels; the global numbered diary has not yet been constructed. -/
def OrderedMarkerCrossOneTypeBelow
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (s : Nat) (U V : FiniteSignRootedNode A n) : Prop :=
  ∀ X Y : FiniteSignRootedNode A n,
    X.1 < Y.1 → Y.1 < s →
      ((F.withOrderedCrossMarkerEdges base before orient).edge X Y U ↔
       (F.withOrderedCrossMarkerEdges base before orient).edge X Y V)

/-- Any RAW singleton parent-type equality across a shared source
cut survives the ordered marker extension, provided the proposed
order respects source levels and the orientation is prefix-uniform.
This includes off-path predecessor vertices and equal-level tie
markers elsewhere in the enlarged relation. -/
theorem orderedMarkerCrossOneType_of_raw_uniform
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (hLevel : F.ExtendsSourceLevels before)
    (hUniform : F.PrefixUniformOrientation orient)
    (i j : ι) (s : Nat)
    (hShared : F.node i s = F.node j s)
    (u v : Nat) (hsu : s ≤ u) (hsv : s ≤ v)
    (hun : u < n) (hvn : v < n)
    (hu : IsLeaf A u) (hv : IsLeaf A v)
    (hRaw : F.RawCrossOneTypeBelow s
      (F.node i u) (F.node j v)) :
    F.OrderedMarkerCrossOneTypeBelow base before orient s
      (F.node i u) (F.node j v) := by
  have hOld := F.markerCrossOneType_of_raw_uniform
    base orient hUniform i j s hShared u v
    hsu hsv hun hvn hu hv hRaw
  intro X Y hXY hYs
  have hYU : Y.1 < (F.node i u).1 := by
    simp only [F.node_level]
    omega
  have hYV : Y.1 < (F.node j v).1 := by
    simp only [F.node_level]
    omega
  have hI := F.orderedMarkerExtension_iff_original_of_source_lt
    base before orient hLevel X Y (F.node i u) hYU
  have hJ := F.orderedMarkerExtension_iff_original_of_source_lt
    base before orient hLevel X Y (F.node j v) hYV
  exact hI.trans ((hOld X Y hXY hYs).trans hJ.symm)

/-- Complete ordered pair parent-type comparison under the
ordered extension: both singleton types and every earlier
auxiliary pair test are included. -/
def OrderedMarkerCrossTwoTypeBelow
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (s : Nat) (U V U' V' : FiniteSignRootedNode A n) : Prop :=
  F.OrderedMarkerCrossOneTypeBelow base before orient s U U' ∧
  F.OrderedMarkerCrossOneTypeBelow base before orient s V V' ∧
  (∀ X : FiniteSignRootedNode A n, X.1 < s →
    ((F.withOrderedCrossMarkerEdges base before orient).edge X U V ↔
     (F.withOrderedCrossMarkerEdges base before orient).edge X U' V'))

/-- Prefix-uniformity lifts any raw cross-branch full pair-type
equality to the corrected ORDERED marker extension. The two
compared leaf pairs need not have the same E3 orientations. -/
theorem orderedMarkerCrossTwoType_of_raw_uniform
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (hLevel : F.ExtendsSourceLevels before)
    (hUniform : F.PrefixUniformOrientation orient)
    (i j : ι) (s : Nat)
    (hShared : F.node i s = F.node j s)
    (u v w z : Nat)
    (hsu : s ≤ u) (hsw : s ≤ w)
    (huv : u < v) (hwz : w < z)
    (hvn : v < n) (hzn : z < n)
    (hu : IsLeaf A u) (hv : IsLeaf A v)
    (hw : IsLeaf A w) (hz : IsLeaf A z)
    (hRaw : F.RawCrossTwoTypeBelow s
      (F.node i u) (F.node i v)
      (F.node j w) (F.node j z)) :
    F.OrderedMarkerCrossTwoTypeBelow base before orient s
      (F.node i u) (F.node i v)
      (F.node j w) (F.node j z) := by
  have hOld := F.markerCrossTwoType_of_raw_uniform
    base orient hUniform i j s hShared
    u v w z hsu hsw huv hwz hvn hzn
    hu hv hw hz hRaw
  refine ⟨
    F.orderedMarkerCrossOneType_of_raw_uniform
      base before orient hLevel hUniform i j s hShared
      u w hsu hsw (by omega) (by omega) hu hw hRaw.1,
    F.orderedMarkerCrossOneType_of_raw_uniform
      base before orient hLevel hUniform i j s hShared
      v z (by omega) (by omega) hvn hzn hv hz hRaw.2.1,
    ?_⟩
  intro X hXs
  have hIU : (F.node i u).1 < (F.node i v).1 := by
    simpa only [F.node_level] using huv
  have hJW : (F.node j w).1 < (F.node j z).1 := by
    simpa only [F.node_level] using hwz
  have hI := F.orderedMarkerExtension_iff_original_of_source_lt
    base before orient hLevel X (F.node i u) (F.node i v) hIU
  have hJ := F.orderedMarkerExtension_iff_original_of_source_lt
    base before orient hLevel X (F.node j w) (F.node j z) hJW
  exact hI.trans ((hOld.2.2 X hXs).trans hJ.symm)

/-- V1 POSITIVE-parent type stability in the actual ORDERED
marker extension, under the precise two conditional hypotheses:
ambient order extends source levels and orientation is prefix-
uniform. All earlier original-level tests are included. -/
theorem orderedMarker_shared_oneSplit_positive_parent
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (hLevel : F.ExtendsSourceLevels before)
    (hUniform : F.PrefixUniformOrientation orient)
    (i j : ι) (s : Nat)
    (hs : IsOneSplit A s)
    (hShared : F.node i s = F.node j s)
    (u v : Nat) (hsu : s < u) (hsv : s < v)
    (hun : u < n) (hvn : v < n)
    (hu : IsLeaf (F.graph i) u)
    (hv : IsLeaf (F.graph j) v)
    (hPosI : (F.graph i).edge 0 s u)
    (hPosJ : (F.graph j).edge 0 s v) :
    F.OrderedMarkerCrossOneTypeBelow base before orient s
      (F.node i u) (F.node j v) := by
  have hRaw := F.raw_shared_oneSplit_positive_parent_compatible
    i j s hs hShared u v hsu hsv hun hvn
    hu hv hPosI hPosJ
  have huA : IsLeaf A u :=
    ((F.flip i).role_iff u hu.1 hun).1.mpr hu
  have hvA : IsLeaf A v :=
    ((F.flip j).role_iff v hv.1 hvn).1.mpr hv
  exact F.orderedMarkerCrossOneType_of_raw_uniform
    base before orient hLevel hUniform i j s hShared
    u v hsu.le hsv.le hun hvn huA hvA hRaw

/-- V2 POSITIVE-parent type stability in the ordered marker
extension under source-level-compatible prefix-uniform choices.
The two current E3 bits are NOT required to agree. -/
theorem orderedMarker_shared_twoSplit_positive_parent
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (hLevel : F.ExtendsSourceLevels before)
    (hUniform : F.PrefixUniformOrientation orient)
    (i j : ι) (s : Nat)
    (hs : IsTwoSplit A s)
    (hShared : F.node i s = F.node j s)
    (u v w z : Nat)
    (huv : u < v) (hwz : w < z)
    (hvn : v < n) (hzn : z < n)
    (hsu : s < u) (hsw : s < w)
    (hu : IsLeaf (F.graph i) u)
    (hv : IsLeaf (F.graph i) v)
    (hw : IsLeaf (F.graph j) w)
    (hz : IsLeaf (F.graph j) z)
    (hPosI : (F.graph i).edge s u v)
    (hPosJ : (F.graph j).edge s w z) :
    F.OrderedMarkerCrossTwoTypeBelow base before orient s
      (F.node i u) (F.node i v)
      (F.node j w) (F.node j z) := by
  have hRaw := F.raw_shared_twoSplit_positive_parent_compatible
    i j s hs hShared u v w z huv hwz hvn hzn
    hsu hsw hu hv hw hz hPosI hPosJ
  have huA : IsLeaf A u :=
    ((F.flip i).role_iff u hu.1 (by omega)).1.mpr hu
  have hvA : IsLeaf A v :=
    ((F.flip i).role_iff v hv.1 hvn).1.mpr hv
  have hwA : IsLeaf A w :=
    ((F.flip j).role_iff w hw.1 (by omega)).1.mpr hw
  have hzA : IsLeaf A z :=
    ((F.flip j).role_iff z hz.1 hzn).1.mpr hz
  exact F.orderedMarkerCrossTwoType_of_raw_uniform
    base before orient hLevel hUniform i j s hShared
    u v w z hsu.le hsw.le huv hwz hvn hzn
    huA hvA hwA hzA hRaw

end FiniteSignRootedFlipFamily
end DiaryLeafPriority
end ThreeUniformDiaries
