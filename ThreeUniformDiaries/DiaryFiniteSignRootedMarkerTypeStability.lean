import ThreeUniformDiaries.DiaryFiniteSignRootedOffBranchPrefix
import ThreeUniformDiaries.DiaryFiniteSignRootedRawCrossType

/-!
# Prefix-uniform Devlin marker choices preserve raw source parent types

The sign-rooted raw tree has verified V1/V2 positive parent-type
agreement at shared source splits. Arbitrary new off-branch Devlin
edges can destroy these types: an earlier off-branch leaf Y may get
different marker-one/two incidences with two positive successors.

This module gives an explicit SUFFICIENT stability condition:
the added orientation is prefix-uniform. Then for corresponding
later source leaves on branches sharing a cut s, all earlier
cross-marker tests agree. The raw singleton-type equality therefore
lifts to the marker-extended graph. The auxiliary pair-type tests
are unchanged because each compared pair already lies together
on an original source branch. The full ordered-pair predecessor
type equivalence follows.

This establishes the V1/V2 TYPE STABILITY half of a possible
gluing proof under an explicit condition. It does NOT establish
literal V3: the prefix-uniform constant orientation may fail
the lexicographic comparison. Equal-original-source-level leaf
pairs need the separate ordered-marker extension as well.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace FiniteSignRootedFlipFamily

variable {A : Ordered3Graph Nat} {n : Nat} {ι : Type*}

/-- Singleton predecessor-type equality in the graph obtained
by adding the first version of cross-branch Devlin markers. -/
def MarkerCrossOneTypeBelow
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (s : Nat)
    (U V : FiniteSignRootedNode A n) : Prop :=
  ∀ X Y : FiniteSignRootedNode A n,
    X.1 < Y.1 → Y.1 < s →
      ((F.withCrossMarkerEdges base orient).edge X Y U ↔
       (F.withCrossMarkerEdges base orient).edge X Y V)

/-- Under a prefix-uniform orientation, two later source leaves
on branches sharing cut s retain EVERY raw predecessor singleton
test equality, including those with an earlier off-path leaf.
This is not merely equality of the selected source codes. -/
theorem markerCrossOneType_of_raw_uniform
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (hUniform : F.PrefixUniformOrientation orient)
    (i j : ι) (s : Nat)
    (hShared : F.node i s = F.node j s)
    (u v : Nat) (hsu : s ≤ u) (hsv : s ≤ v)
    (hun : u < n) (hvn : v < n)
    (hu : IsLeaf A u) (hv : IsLeaf A v)
    (hRaw : F.RawCrossOneTypeBelow s
      (F.node i u) (F.node j v)) :
    F.MarkerCrossOneTypeBelow base orient s
      (F.node i u) (F.node j v) := by
  classical
  intro X Y hXY hYs
  have hRawTest := hRaw X Y hXY hYs
  have hOff := F.offBranchLeafPair_iff_of_shared_cut
    i j s hShared Y hYs u v hsu hsv hun hvn hu hv
  have hM1 :
      (X = F.node base 1 ∧
        F.OffBranchLeafPair Y (F.node i u) ∧
        orient Y (F.node i u)) ↔
      (X = F.node base 1 ∧
        F.OffBranchLeafPair Y (F.node j v) ∧
        orient Y (F.node j v)) := by
    constructor
    · rintro ⟨hx,hoff,hor⟩
      have hOrient := hUniform i j s hShared
        Y u v hYs hsu hsv hun hvn hoff.leafY hu hv
      exact ⟨hx,hOff.mp hoff,hOrient.mp hor⟩
    · rintro ⟨hx,hoff,hor⟩
      have hOrient := hUniform i j s hShared
        Y u v hYs hsu hsv hun hvn hoff.leafY hu hv
      exact ⟨hx,hOff.mpr hoff,hOrient.mpr hor⟩
  have hM2 :
      (X = F.node base 2 ∧
        F.OffBranchLeafPair Y (F.node i u) ∧
        ¬ orient Y (F.node i u)) ↔
      (X = F.node base 2 ∧
        F.OffBranchLeafPair Y (F.node j v) ∧
        ¬ orient Y (F.node j v)) := by
    constructor
    · rintro ⟨hx,hoff,hor⟩
      have hOrient := hUniform i j s hShared
        Y u v hYs hsu hsv hun hvn hoff.leafY hu hv
      exact ⟨hx,hOff.mp hoff,(not_congr hOrient).mp hor⟩
    · rintro ⟨hx,hoff,hor⟩
      have hOrient := hUniform i j s hShared
        Y u v hYs hsu hsv hun hvn hoff.leafY hu hv
      exact ⟨hx,hOff.mpr hoff,(not_congr hOrient).mpr hor⟩
  change
    ((F.rawAmalgam).edge X Y (F.node i u) ∨
      (X = F.node base 1 ∧
        F.OffBranchLeafPair Y (F.node i u) ∧
        orient Y (F.node i u)) ∨
      (X = F.node base 2 ∧
        F.OffBranchLeafPair Y (F.node i u) ∧
        ¬ orient Y (F.node i u))) ↔
    ((F.rawAmalgam).edge X Y (F.node j v) ∨
      (X = F.node base 1 ∧
        F.OffBranchLeafPair Y (F.node j v) ∧
        orient Y (F.node j v)) ∨
      (X = F.node base 2 ∧
        F.OffBranchLeafPair Y (F.node j v) ∧
        ¬ orient Y (F.node j v)))
  exact or_congr hRawTest (or_congr hM1 hM2)

/-- Cross-marker additions do not affect ANY raw test whose
two terminal leaves already belong to a common original branch.
In particular all auxiliary pair-type tests within a branch
are unchanged, regardless of the new orientation. -/
theorem markerCross_aux_eq_raw_on_branch
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (i : ι) (u v : Nat)
    (huv : u < v) (hvn : v < n)
    (X : FiniteSignRootedNode A n) :
    (F.withCrossMarkerEdges base orient).edge
      X (F.node i u) (F.node i v) ↔
    (F.rawAmalgam).edge X (F.node i u) (F.node i v) := by
  have hShared : F.SharedBranchPair
      (F.node i u) (F.node i v) :=
    ⟨i,u,v,huv,hvn,rfl,rfl⟩
  have hNotOff :
      ¬ F.OffBranchLeafPair (F.node i u) (F.node i v) := by
    intro h
    exact h.separated hShared
  change
    ((F.rawAmalgam).edge X (F.node i u) (F.node i v) ∨
      (X = F.node base 1 ∧
        F.OffBranchLeafPair (F.node i u) (F.node i v) ∧
        orient (F.node i u) (F.node i v)) ∨
      (X = F.node base 2 ∧
        F.OffBranchLeafPair (F.node i u) (F.node i v) ∧
        ¬ orient (F.node i u) (F.node i v))) ↔
    (F.rawAmalgam).edge X (F.node i u) (F.node i v)
  simp only [hNotOff, false_and, and_false, or_false, iff_self]

/-- The complete predecessor ordered-pair comparison after
marker additions, covering both singleton coordinate codes
and every auxiliary ordered-pair test. -/
def MarkerCrossTwoTypeBelow
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (s : Nat)
    (U V U' V' : FiniteSignRootedNode A n) : Prop :=
  F.MarkerCrossOneTypeBelow base orient s U U' ∧
  F.MarkerCrossOneTypeBelow base orient s V V' ∧
  (∀ X : FiniteSignRootedNode A n, X.1 < s →
    ((F.withCrossMarkerEdges base orient).edge X U V ↔
     (F.withCrossMarkerEdges base orient).edge X U' V'))

/-- Under prefix uniformity, the RAW cross-branch full pair
predecessor type equivalence survives added marker edges.
The source pair coordinates are ordered within each branch,
so no new auxiliary pair test is introduced by the extension. -/
theorem markerCrossTwoType_of_raw_uniform
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
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
    F.MarkerCrossTwoTypeBelow base orient s
      (F.node i u) (F.node i v)
      (F.node j w) (F.node j z) := by
  refine ⟨
    F.markerCrossOneType_of_raw_uniform
      base orient hUniform i j s hShared
      u w hsu hsw (by omega) (by omega)
      hu hw hRaw.1,
    F.markerCrossOneType_of_raw_uniform
      base orient hUniform i j s hShared
      v z (by omega) (by omega) hvn hzn
      hv hz hRaw.2.1,
    ?_⟩
  intro X hXs
  have hI := F.markerCross_aux_eq_raw_on_branch
    base orient i u v huv hvn X
  have hJ := F.markerCross_aux_eq_raw_on_branch
    base orient j w z hwz hzn X
  exact hI.trans ((hRaw.2.2 X hXs).trans hJ.symm)

end FiniteSignRootedFlipFamily
end DiaryLeafPriority
end ThreeUniformDiaries
