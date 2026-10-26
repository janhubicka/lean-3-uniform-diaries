import ThreeUniformDiaries.DiaryFiniteSignRootedOrderedParentStability
import ThreeUniformDiaries.DiaryFiniteSignRootedSameLevelSplitTests
import ThreeUniformDiaries.DiaryFiniteSignRootedOrderedCutSupport
import ThreeUniformDiaries.DiaryFiniteCanonicalSignRootedOrder

/-!
# Positive-parent type transport to the actual level-first rank cut

Existing cross-branch compatibility lemmas compare predecessor tests
below an ORIGINAL source level s. A level-first enumeration of the
finite sign-rooted carrier can place other nodes of original level s
before the shared split node, and can tie the first two coordinates
of an earlier edge test.

This module closes both discrepancies. A monotone, irreflexive order
on the raw nodes gives all earlier rank-cut predecessors original
level at most s. Strictly earlier levels use the verified source-cut
type comparison; same-level middle-coordinate tests vanish by the
off-path split lemma; tied first-coordinate tests vanish by the
strict original-level support theorem; and same-level auxiliary
first-coordinate tests vanish by the second off-path lemma.

These are conditional V1/V2 POSITIVE PARENT comparisons. They do not
construct an orientation satisfying literal V3, a complete pre-diary
or a finite every-flip absorber.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace FiniteSignRootedFlipFamily

variable {A : Ordered3Graph Nat} {n : Nat} {ι : Type*}

/-- Precisely the ordering properties required to turn a source-level
cut into a finite-rank cut: the order never decreases original source
levels, and no node precedes itself. Totality is not needed here. -/
def LevelFirstStrictOrder
    (F : FiniteSignRootedFlipFamily A n ι)
    (before : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop) : Prop :=
  (∀ X Y : FiniteSignRootedNode A n,
    before X Y → X.1 ≤ Y.1) ∧
  (∀ X : FiniteSignRootedNode A n, ¬ before X X)

/-- Singleton predecessor tests at the ACTUAL ordering cut
just before the shared node representing source split s. -/
def OrderedMarkerRankOneTypeAtSplit
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (i : ι) (s : Nat)
    (U V : FiniteSignRootedNode A n) : Prop :=
  ∀ X Y : FiniteSignRootedNode A n,
    before X Y → before Y (F.node i s) →
      ((F.withOrderedCrossMarkerEdges base before orient).edge X Y U ↔
       (F.withOrderedCrossMarkerEdges base before orient).edge X Y V)

/-- Source-cut agreement and the two same-level zero tests imply
genuine rank-cut singleton predecessor agreement at a shared split.
The endpoints may come from different genuine flips. -/
theorem orderedMarker_rankOneType_of_source_cut
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (hOrder : F.LevelFirstStrictOrder before)
    (i j : ι) (s u v : Nat)
    (hs : IsOneSplit A s ∨ IsTwoSplit A s)
    (hShared : F.node i s = F.node j s)
    (hSource : F.OrderedMarkerCrossOneTypeBelow
      base before orient s (F.node i u) (F.node j v)) :
    F.OrderedMarkerRankOneTypeAtSplit base before orient i s
      (F.node i u) (F.node j v) := by
  intro X Y hXY hYS
  have hYs : Y.1 ≤ s := by
    have h := hOrder.1 Y (F.node i s) hYS
    simpa only [F.node_level] using h
  rcases lt_or_eq_of_le hYs with hYsLt | hYsEq
  · have hXle : X.1 ≤ Y.1 := hOrder.1 X Y hXY
    rcases lt_or_eq_of_le hXle with hXYlt | hXYeq
    · exact hSource X Y hXYlt hYsLt
    · have hNoI :
          ¬ (F.withOrderedCrossMarkerEdges base before orient).edge
              X Y (F.node i u) := by
        intro he
        have hStrict := F.orderedMarker_edge_first_level_lt_second
          base before orient X Y (F.node i u) he
        omega
      have hNoJ :
          ¬ (F.withOrderedCrossMarkerEdges base before orient).edge
              X Y (F.node j v) := by
        intro he
        have hStrict := F.orderedMarker_edge_first_level_lt_second
          base before orient X Y (F.node j v) he
        omega
      exact iff_of_false hNoI hNoJ
  · have hDifferent : Y ≠ F.node i s := by
      intro hEq
      have hLoop : before (F.node i s) (F.node i s) := by
        simpa only [hEq] using hYS
      exact (hOrder.2 (F.node i s)) hLoop
    exact F.orderedMarker_sharedSplit_sameLevel_tests_agree
      base before orient i j s u v hs hShared
      Y hYsEq hDifferent X

/-- Full pair-type rank-cut agreement: both singleton coordinates
and all auxiliary predecessor tests are compared at actual ranks. -/
def OrderedMarkerRankTwoTypeAtSplit
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (i : ι) (s : Nat)
    (U V U' V' : FiniteSignRootedNode A n) : Prop :=
  F.OrderedMarkerRankOneTypeAtSplit base before orient i s U U' ∧
  F.OrderedMarkerRankOneTypeAtSplit base before orient i s V V' ∧
  (∀ X : FiniteSignRootedNode A n, before X (F.node i s) →
    ((F.withOrderedCrossMarkerEdges base before orient).edge X U V ↔
     (F.withOrderedCrossMarkerEdges base before orient).edge X U' V'))

/-- Source-cut full-pair agreement extends through all additional
rank-cut tests, including raw nodes tied with a shared 2-split. -/
theorem orderedMarker_rankTwoType_of_source_cut
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (hOrder : F.LevelFirstStrictOrder before)
    (i j : ι) (s u v w z : Nat)
    (hs : IsOneSplit A s ∨ IsTwoSplit A s)
    (hShared : F.node i s = F.node j s)
    (hSource : F.OrderedMarkerCrossTwoTypeBelow
      base before orient s
      (F.node i u) (F.node i v)
      (F.node j w) (F.node j z)) :
    F.OrderedMarkerRankTwoTypeAtSplit base before orient i s
      (F.node i u) (F.node i v)
      (F.node j w) (F.node j z) := by
  refine ⟨
    F.orderedMarker_rankOneType_of_source_cut
      base before orient hOrder i j s u w hs hShared hSource.1,
    F.orderedMarker_rankOneType_of_source_cut
      base before orient hOrder i j s v z hs hShared hSource.2.1,
    ?_⟩
  intro X hXS
  have hXle : X.1 ≤ s := by
    have h := hOrder.1 X (F.node i s) hXS
    simpa only [F.node_level] using h
  rcases lt_or_eq_of_le hXle with hXs | hXeq
  · exact hSource.2.2 X hXs
  · have hDifferent : X ≠ F.node i s := by
      intro hEq
      have hLoop : before (F.node i s) (F.node i s) := by
        simpa only [hEq] using hXS
      exact (hOrder.2 (F.node i s)) hLoop
    exact F.orderedMarker_sharedSplit_sameLevel_aux_tests_agree
      base before orient i j s u v w z hs hShared
      X hXeq hDifferent

/-- Verified positive V1 parent-type comparison at the actual rank
cut, CONDITIONAL on source-level monotonicity, order irreflexivity
and prefix-uniform Devlin marker orientation. -/
theorem orderedMarker_shared_oneSplit_rank_parent
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (hLevel : F.ExtendsSourceLevels before)
    (hOrder : F.LevelFirstStrictOrder before)
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
    F.OrderedMarkerRankOneTypeAtSplit base before orient i s
      (F.node i u) (F.node j v) := by
  apply F.orderedMarker_rankOneType_of_source_cut
    base before orient hOrder i j s u v (Or.inl hs) hShared
  exact F.orderedMarker_shared_oneSplit_positive_parent
    base before orient hLevel hUniform i j s hs hShared
    u v hsu hsv hun hvn hu hv hPosI hPosJ

/-- Verified positive V2 parent-type comparison at the actual rank
cut; opposite current E3 bits are allowed, provided the orientation
is prefix-uniform and the order is level-first and irreflexive. -/
theorem orderedMarker_shared_twoSplit_rank_parent
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (hLevel : F.ExtendsSourceLevels before)
    (hOrder : F.LevelFirstStrictOrder before)
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
    F.OrderedMarkerRankTwoTypeAtSplit base before orient i s
      (F.node i u) (F.node i v)
      (F.node j w) (F.node j z) := by
  apply F.orderedMarker_rankTwoType_of_source_cut
    base before orient hOrder i j s u v w z (Or.inr hs) hShared
  exact F.orderedMarker_shared_twoSplit_positive_parent
    base before orient hLevel hUniform i j s hs hShared
    u v w z huv hwz hvn hzn hsu hsw
    hu hv hw hz hPosI hPosJ

end FiniteSignRootedFlipFamily

/-- The canonical level-first ambient order never decreases source
levels, even on raw nodes outside the realised finite carrier. -/
theorem finiteCanonicalNodeBeforeAmbient_level_mono
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (X Y : FiniteSignRootedNode A n)
    (h : finiteCanonicalNodeBeforeAmbient DA X Y) :
    X.1 ≤ Y.1 := by
  change X.1 < Y.1 ∨
    (X.1 = Y.1 ∧ finiteCanonicalNodeBeforeExternal DA X Y) at h
  rcases h with hLt | ⟨hEq,_⟩
  · exact Nat.le_of_lt hLt
  · exact le_of_eq hEq

/-- Irreflexivity holds on all raw nodes, not just the actual
finite canonical carrier. -/
theorem finiteCanonicalNodeBeforeAmbient_irrefl
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (X : FiniteSignRootedNode A n) :
    ¬ finiteCanonicalNodeBeforeAmbient DA X X := by
  intro h
  change X.1 < X.1 ∨
    (X.1 = X.1 ∧ finiteCanonicalNodeBeforeExternal DA X X) at h
  rcases h with hLt | ⟨_,hExternal⟩
  · omega
  · rcases hExternal with ⟨hx,hy,hBefore⟩
    have hSelf : finiteCanonicalNodeBefore DA
        (⟨X,hx⟩ : FiniteCanonicalSignRootedVertex DA)
        (⟨X,hx⟩ : FiniteCanonicalSignRootedVertex DA) := by
      simpa using hBefore
    exact (finiteCanonicalNodeBefore_irrefl DA ⟨X,hx⟩) hSelf

/-- The concrete finite canonical level-first ordering discharges
BOTH order hypotheses used by the rank-cut V1/V2 bridge. -/
theorem finiteCanonicalNodeBeforeAmbient_levelFirstStrictOrder
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    (finiteCanonicalSignRootedFamily DA).LevelFirstStrictOrder
      (finiteCanonicalNodeBeforeAmbient DA) := by
  constructor
  · intro X Y hXY
    exact finiteCanonicalNodeBeforeAmbient_level_mono DA X Y hXY
  · intro X
    exact finiteCanonicalNodeBeforeAmbient_irrefl DA X

end DiaryLeafPriority
end ThreeUniformDiaries
