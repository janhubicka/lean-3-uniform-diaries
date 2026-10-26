import ThreeUniformDiaries.DiaryFiniteCanonicalRankedRawLex
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalOriginalOneMeet
import ThreeUniformDiaries.DiaryFiniteCanonicalExactMarkerRanks

/-!
# The ACTUAL causal sign-rooted graph satisfies literal V3 on each source branch

The three old markers are proved to have exactly Nat indices 0, 1, 2.
The constructed causal extension preserves every original source
flip branch inducedly, including all marker edge incidences.

At an original proper leaf singleton meet, the ranked RAW graph
has the exact old meet and pointed auxiliary meet; hence the RAW
literal LexEarlier equals the source diary's literal LexEarlier.
The final causal graph preserves this RAW LexEarlier exactly.

We combine these results with the genuine finite source-flip diary
V3 fields to prove BOTH LITERAL final marker equivalences on
EVERY ordered pair of original source leaves. No source leaf pair
requires an assumed prefix-uniform orientation or an independent
marker axiom in the completed graph.

The off-branch pairs have already been handled separately.
The complete V3 theorem for all ACTUAL target leaves will also
require proving a census of which finite ranked vertices are leaves.
V1/V2, role witnesses, finite S-meets and absorption remain open.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The literal first and second Devlin marker bits of an
original canonical source flip are reflected exactly in the
FINAL causal graph. The marker indices are literally 1,2,
not just order-equivalent to their source positions. -/
theorem finiteCanonicalCausalMarkerGraph_original_marker_bits
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (u v : Nat) (huv : u < v) (hvn : v < n)
    (hu : IsLeaf A u) :
    ((finiteCanonicalCausalMarkerGraph DA).edge 1
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i u (by omega))).val
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i v hvn)).val ↔
      ((finiteCanonicalSignRootedFamily DA).graph i).edge 1 u v) ∧
    ((finiteCanonicalCausalMarkerGraph DA).edge 2
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i u (by omega))).val
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i v hvn)).val ↔
      ((finiteCanonicalSignRootedFamily DA).graph i).edge 2 u v) := by
  have hn : 3 ≤ n := DA.prediary.frame.length_ge_three
  have h1u : 1 < u := by have h := hu.1; omega
  have h2u : 2 < u := by have h := hu.1; omega
  have hMarker1 :
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i 1 (by omega))).val = 1 :=
    finiteCanonicalMarker_one_rank DA i
  have hMarker2 :
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i 2 (by omega))).val = 2 :=
    finiteCanonicalMarker_two_rank DA i
  constructor
  · have h := finiteCanonicalCausalMarkerGraph_branch_edge_iff
      DA i 1 u v h1u huv hvn
    simpa only [hMarker1] using h
  · have h := finiteCanonicalCausalMarkerGraph_branch_edge_iff
      DA i 2 u v h2u huv hvn
    simpa only [hMarker2] using h

/-- BOTH full literal V3 marker equivalences hold in the
ACTUAL completed causal sign-rooted graph for EVERY ordered
source-leaf pair of a genuine canonical flip branch. -/
theorem finiteCanonicalCausalMarkerGraph_original_branch_V3
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (u v : Nat) (huv : u < v) (hvn : v < n)
    (hu : IsLeaf A u) (hv : IsLeaf A v) :
    ((finiteCanonicalCausalMarkerGraph DA).edge 1
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i u (by omega))).val
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i v hvn)).val ↔
      LexEarlier (finiteCanonicalCausalMarkerGraph DA)
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i u (by omega))).val
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i v hvn)).val) ∧
    ((finiteCanonicalCausalMarkerGraph DA).edge 2
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i u (by omega))).val
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i v hvn)).val ↔
      ¬ LexEarlier (finiteCanonicalCausalMarkerGraph DA)
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i u (by omega))).val
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i v hvn)).val) := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let R := finiteCanonicalRankedRawGraph DA
  let G := finiteCanonicalCausalMarkerGraph DA
  have hun : u < n := by omega
  have huTarget : IsLeaf (F.graph i) u :=
    ((F.flip i).role_iff u hu.1 hun).1.mp hu
  have hvTarget : IsLeaf (F.graph i) v :=
    ((F.flip i).role_iff v hv.1 hvn).1.mp hv
  let s := (F.graph i).oneMeetLevel u v
  have hSourceMeet : (F.graph i).oneMeetLevel u v = s := rfl
  have hsTarget : IsOneSplit (F.graph i) s :=
    (F.flip i).target_diary.singleton_meets
      u v huv hvn huTarget hvTarget
  have hsn : s < n :=
    (F.flip i).target_diary.prediary.oneSplit_lt s hsTarget
  have hsSource : IsOneSplit A s :=
    ((F.flip i).role_iff s hsTarget.1 hsn).2.1.mpr hsTarget
  have hBound : s ≤ min u v :=
    (F.graph i).oneMeetLevel_le_min u v
  have hNeU : s ≠ u := by
    intro hEq
    have hSU : IsOneSplit (F.graph i) u := by
      simpa only [hEq] using hsTarget
    exact huTarget.2.1 hSU.2.1
  have hNeV : s ≠ v := by
    intro hEq
    have hSV : IsOneSplit (F.graph i) v := by
      simpa only [hEq] using hsTarget
    exact hvTarget.2.1 hSV.2.1
  have hsu : s < u := by
    have hle : s ≤ u := hBound.trans (min_le_left _ _)
    omega
  have hsv : s < v := by
    have hle : s ≤ v := hBound.trans (min_le_right _ _)
    omega
  let a := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i u hun)).val
  let b := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i v hvn)).val
  have hFinalRaw : LexEarlier G a b ↔ LexEarlier R a b :=
    finiteCanonicalCausalMarkerGraph_original_lex_iff_rankedRaw
      DA i s u v hsSource hsn hsu hsv hun hvn hu hv hSourceMeet
  have hRawSource :
      LexEarlier R a b ↔ LexEarlier (F.graph i) u v :=
    finiteCanonicalRankedRaw_original_lex_iff_source
      DA i s u v hsn hsu hsv hun hvn hSourceMeet
  have hFinalSource : LexEarlier G a b ↔
      LexEarlier (F.graph i) u v :=
    hFinalRaw.trans hRawSource
  have hSourceV3One : (F.graph i).edge 1 u v ↔
      LexEarlier (F.graph i) u v :=
    (F.flip i).target_diary.prediary.leaf_marker_one
      u v huv hvn huTarget hvTarget
  have hSourceV3Two : (F.graph i).edge 2 u v ↔
      ¬ LexEarlier (F.graph i) u v :=
    (F.flip i).target_diary.prediary.leaf_marker_two
      u v huv hvn huTarget hvTarget
  have hMarkers :=
    finiteCanonicalCausalMarkerGraph_original_marker_bits
      DA i u v huv hvn hu
  exact ⟨
    (hMarkers.1.trans hSourceV3One).trans hFinalSource.symm,
    (hMarkers.2.trans hSourceV3Two).trans
      (not_congr hFinalSource.symm)⟩

end DiaryLeafPriority
end ThreeUniformDiaries
