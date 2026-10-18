import ThreeUniformDiaries.DiaryFiniteProtectedMeetPicture

/-!
# Adjoining the three distinguished markers to protected finite pictures

The finite protected meet-picture interface initially treats only
original vertices at levels >= 3. A finite diary also contains
markers 0,1,2. These require no extra splitting assumptions:
any singleton or full pair-type meet CAPPED below level three is
already computed entirely from the original marker prefix.

The one-pass map fixes 0,1,2 and the induced old copy preserves
all their edges. Therefore it preserves those small capped
numerical meets exactly. Adding the marker set to a protected
finite carrier preserves ALL singleton and full ordered-pair
numerical meets among the enlarged finite carrier.

The output is a countable completed diary with a finite protected
induced picture; this does not construct a finite target diary
or a simultaneous ambient pre-diary for every flip.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat} {F : Finset Nat}

/-- Exact numerical one-meet preservation whenever the source cap
lies strictly below the first new-event level three. This holds
without ANY V/E/S assumption on the original hypergraph. -/
theorem onePass_markerCapped_oneMeet_preserved
    (H : Ordered3Graph Nat) (u v : Nat)
    (hSmall : min u v < 3) :
    (onePassRawTarget H).oneMeetLevel
        (onePassOldImage H u) (onePassOldImage H v) =
      onePassOldImage H (H.oneMeetLevel u v) := by
  classical
  let G := onePassRawTarget H
  let f := onePassOldImage H
  let w := H.oneMeetLevel u v
  let z := G.oneMeetLevel (f u) (f v)
  have hCapTarget : min (f u) (f v) = min u v := by
    calc
      min (f u) (f v) = f (min u v) :=
        (onePassOldImage_min H u v).symm
      _ = min u v :=
        onePassOldImage_fixed_below_three H (min u v) hSmall
  have hSourceBound : w ≤ min u v := H.oneMeetLevel_le_min u v
  have hTargetBound : z ≤ min (f u) (f v) :=
    G.oneMeetLevel_le_min (f u) (f v)
  have hw3 : w < 3 := by omega
  have hz3 : z < 3 := by omega
  have hAtW : G.SameOneTypeBelow w (f u) (f v) :=
    (onePass_oneTypeBelow_markerCut_iff H w u v (by omega)).mp
      (H.oneMeetLevel_agree u v)
  have hAtZ : H.SameOneTypeBelow z u v :=
    (onePass_oneTypeBelow_markerCut_iff H z u v (by omega)).mpr
      (G.oneMeetLevel_agree (f u) (f v))
  have hwle : w ≤ z :=
    Nat.le_findGreatest (by omega : w ≤ min (f u) (f v)) hAtW
  have hzle : z ≤ w :=
    Nat.le_findGreatest (by omega : z ≤ min u v) hAtZ
  have heq : z = w := by omega
  calc
    G.oneMeetLevel (f u) (f v) = w := heq
    _ = f w := (onePassOldImage_fixed_below_three H w hw3).symm
    _ = f (H.oneMeetLevel u v) := rfl

/-- Exact numerical full two-meet preservation whenever the
capping first coordinate lies below marker cut three.
The original pair roles and all source diary axioms are irrelevant. -/
theorem onePass_markerCapped_twoMeet_preserved
    (H : Ordered3Graph Nat) (a b c d : Nat)
    (hSmall : min a c < 3) :
    (onePassRawTarget H).twoMeetLevel
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) =
      onePassOldImage H (H.twoMeetLevel a b c d) := by
  classical
  let G := onePassRawTarget H
  let f := onePassOldImage H
  let w := H.twoMeetLevel a b c d
  let z := G.twoMeetLevel (f a) (f b) (f c) (f d)
  have hCapTarget : min (f a) (f c) = min a c := by
    calc
      min (f a) (f c) = f (min a c) :=
        (onePassOldImage_min H a c).symm
      _ = min a c :=
        onePassOldImage_fixed_below_three H (min a c) hSmall
  have hSourceBound : w ≤ min a c := H.twoMeetLevel_le_min a b c d
  have hTargetBound : z ≤ min (f a) (f c) :=
    G.twoMeetLevel_le_min (f a) (f b) (f c) (f d)
  have hw3 : w < 3 := by omega
  have hz3 : z < 3 := by omega
  have hAtW : G.SameTwoTypeBelow w (f a) (f b) (f c) (f d) :=
    (onePass_twoTypeBelow_markerCut_iff H w a b c d (by omega)).mp
      (H.twoMeetLevel_agree a b c d)
  have hAtZ : H.SameTwoTypeBelow z a b c d :=
    (onePass_twoTypeBelow_markerCut_iff H z a b c d (by omega)).mpr
      (G.twoMeetLevel_agree (f a) (f b) (f c) (f d))
  have hwle : w ≤ z :=
    Nat.le_findGreatest (by omega : w ≤ min (f a) (f c)) hAtW
  have hzle : z ≤ w :=
    Nat.le_findGreatest (by omega : z ≤ min a c) hAtZ
  have heq : z = w := by omega
  calc
    G.twoMeetLevel (f a) (f b) (f c) (f d) = w := heq
    _ = f w := (onePassOldImage_fixed_below_three H w hw3).symm
    _ = f (H.twoMeetLevel a b c d) := rfl

/-- The finite original carrier with the three distinguished
markers 0,1,2 adjoined. -/
def finiteProtectedWithMarkers (F : Finset Nat) : Finset Nat :=
  Finset.range 3 ∪ F

/-- All nonmarker members of the enlarged finite carrier already
belong to the protected nonmarker carrier. -/
theorem finiteProtectedWithMarkers_nonmarker
    (F : Finset Nat) (u : Nat)
    (hu : u ∈ finiteProtectedWithMarkers F) (hu3 : 3 ≤ u) :
    u ∈ F := by
  change u ∈ Finset.range 3 ∪ F at hu
  rcases Finset.mem_union.mp hu with hMarker | hF
  · have hlt : u < 3 := Finset.mem_range.mp hMarker
    omega
  · exact hF

/-- Every singleton meet on the marked finite carrier is retained
literally under one-pass completion, including comparisons with
marker vertices themselves. -/
theorem onePass_finiteProtectedWithMarkers_oneMeet
    (P : RolePrediary H) (Q : FiniteProtectedMeetPicture H F) :
    ∀ u v : Nat,
      u ∈ finiteProtectedWithMarkers F →
      v ∈ finiteProtectedWithMarkers F →
      (onePassRawTarget H).oneMeetLevel
          (onePassOldImage H u) (onePassOldImage H v) =
        onePassOldImage H (H.oneMeetLevel u v) := by
  intro u v hu hv
  by_cases hSmall : min u v < 3
  · exact onePass_markerCapped_oneMeet_preserved H u v hSmall
  · have hu3 : 3 ≤ u := by omega
    have hv3 : 3 ≤ v := by omega
    exact onePass_finiteProtected_oneMeet_preserved P Q u v
      (finiteProtectedWithMarkers_nonmarker F u hu hu3)
      (finiteProtectedWithMarkers_nonmarker F v hv hv3)

/-- Every ordered full two-type meet on the marked finite carrier
is retained literally, covering the early-marker case as well as
all leaf/leaf, mixed/mixed and cross-role nonmarker cases. -/
theorem onePass_finiteProtectedWithMarkers_twoMeet
    (P : RolePrediary H) (Q : FiniteProtectedMeetPicture H F) :
    ∀ a b c d : Nat,
      a ∈ finiteProtectedWithMarkers F →
      b ∈ finiteProtectedWithMarkers F →
      c ∈ finiteProtectedWithMarkers F →
      d ∈ finiteProtectedWithMarkers F →
      a < b → c < d →
      (onePassRawTarget H).twoMeetLevel
          (onePassOldImage H a) (onePassOldImage H b)
          (onePassOldImage H c) (onePassOldImage H d) =
        onePassOldImage H (H.twoMeetLevel a b c d) := by
  intro a b c d ha hb hc hd hab hcd
  by_cases hSmall : min a c < 3
  · exact onePass_markerCapped_twoMeet_preserved H a b c d hSmall
  · have ha3 : 3 ≤ a := by omega
    have hc3 : 3 ≤ c := by omega
    have hb3 : 3 ≤ b := by omega
    have hd3 : 3 ≤ d := by omega
    exact onePass_finiteProtected_twoMeet_preserved P Q
      a b c d
      (finiteProtectedWithMarkers_nonmarker F a ha ha3)
      (finiteProtectedWithMarkers_nonmarker F b hb hb3)
      (finiteProtectedWithMarkers_nonmarker F c hc hc3)
      (finiteProtectedWithMarkers_nonmarker F d hd hd3)
      hab hcd

/-- FULL relative protected finite-picture embedding, including the
three distinguished markers: the actual old-copy embedding is
increasing and induced, its target is a genuine RoleDiary, and it
preserves every numerical singleton and full ordered-pair meet
inside this enlarged FINITE set. No claim of finite target size
or global every-flip absorption is made. -/
theorem onePass_markedFiniteProtected_inducedEmbedding
    (P : RolePrediary H) (Q : FiniteProtectedMeetPicture H F) :
    ∃ f : Ordered3Graph.Embedding H (onePassRawTarget H),
      RoleDiary (onePassRawTarget H) ∧
      (∀ u v : Nat,
        u ∈ finiteProtectedWithMarkers F →
        v ∈ finiteProtectedWithMarkers F →
        (onePassRawTarget H).oneMeetLevel (f u) (f v) =
          f (H.oneMeetLevel u v)) ∧
      (∀ a b c d : Nat,
        a ∈ finiteProtectedWithMarkers F →
        b ∈ finiteProtectedWithMarkers F →
        c ∈ finiteProtectedWithMarkers F →
        d ∈ finiteProtectedWithMarkers F →
        a < b → c < d →
        (onePassRawTarget H).twoMeetLevel
            (f a) (f b) (f c) (f d) =
          f (H.twoMeetLevel a b c d)) := by
  refine ⟨onePassRawEmbedding H, onePassRawTarget_isDiary P, ?_, ?_⟩
  · intro u v hu hv
    exact onePass_finiteProtectedWithMarkers_oneMeet P Q u v hu hv
  · intro a b c d ha hb hc hd hab hcd
    exact onePass_finiteProtectedWithMarkers_twoMeet P Q
      a b c d ha hb hc hd hab hcd

end DiaryLeafPriority
end ThreeUniformDiaries
