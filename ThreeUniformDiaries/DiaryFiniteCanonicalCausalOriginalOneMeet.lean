import ThreeUniformDiaries.DiaryFiniteCanonicalRankedRawOneMeet
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalMarkerGraph
import ThreeUniformDiaries.DiaryCausalOriginalMeetPreservation

/-!
# Exact old singleton meets in the actual causal sign-rooted graph

The canonical RAW sign-rooted graph preserves each proper original
singleton meet at the exact level-first Nat rank (#905).
The actual off-branch mask agrees at every earlier rank of the
source 1-split (#902) and selects no split-middle column.
The generic causal completion therefore preserves that exact meet.

This proves the exact result for the final concrete completed
graph, not merely an arbitrary conditional marker orientation.

The literal LexEarlier comparison of original branch leaf pairs
is consequently unchanged between the ranked RAW graph and
the final causal graph. Transporting LexEarlier further back to
the source diary is the next independent obligation. Neither
a full finite pre-diary nor flip absorption is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The proper singleton meet of two source-flip leaves is exactly
the finite rank of their old 1-split, even after literal-V3
causal marker insertion in the final sign-rooted graph. -/
theorem finiteCanonicalCausalMarkerGraph_original_proper_oneMeet_exact
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (s u v : Nat)
    (hs : IsOneSplit A s)
    (hsn : s < n) (hsu : s < u) (hsv : s < v)
    (hun : u < n) (hvn : v < n)
    (hu : IsLeaf A u) (hv : IsLeaf A v)
    (hSourceMeet :
      ((finiteCanonicalSignRootedFamily DA).graph i).oneMeetLevel
        u v = s) :
    (finiteCanonicalCausalMarkerGraph DA).oneMeetLevel
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u hun)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i v hvn)).val =
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val := by
  let R := finiteCanonicalRankedRawGraph DA
  let M := finiteCanonicalRankedOffBranchMask DA
  let m := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i s hsn)).val
  let a := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i u hun)).val
  let b := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i v hvn)).val
  have hma : m < a :=
    finiteCanonicalNodeAt_index_lt DA i s u hsu hun
  have hmb : m < b :=
    finiteCanonicalNodeAt_index_lt DA i s v hsv hvn
  have hRaw : R.oneMeetLevel a b = m :=
    finiteCanonicalRankedRaw_original_proper_oneMeet_exact
      DA i s u v hsn hsu hsv hun hvn hSourceMeet
  have hMask : SameEarlierMarkerMask M m a b :=
    finiteCanonicalRankedOffBranchMask_sharedSplit_below
      DA i i s u v (Or.inl hs) hsn rfl hsu hsv hun hvn hu hv
  have hNoMask : ∀ z : Nat, ¬ M m z := by
    intro z
    exact finiteCanonicalRankedOffBranchMask_split_middle_false
      DA i s (Or.inl hs) hsn z
  have hLater : ∀ y z, M y z → y < z :=
    finiteCanonicalRankedOffBranchMask_later DA
  change (causalMarkerLimit R M).oneMeetLevel a b = m
  exact causalMarkerLimit_preserves_original_proper_oneMeet
    R M hLater m a b hma hmb hRaw hMask hNoMask

/-- The literal lexicographic comparison on any old leaf pair
with a genuine singleton split is unchanged by inserting the
actual sign-rooted cross-branch marker edges. -/
theorem finiteCanonicalCausalMarkerGraph_original_lex_iff_rankedRaw
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (s u v : Nat)
    (hs : IsOneSplit A s)
    (hsn : s < n) (hsu : s < u) (hsv : s < v)
    (hun : u < n) (hvn : v < n)
    (hu : IsLeaf A u) (hv : IsLeaf A v)
    (hSourceMeet :
      ((finiteCanonicalSignRootedFamily DA).graph i).oneMeetLevel
        u v = s) :
    LexEarlier (finiteCanonicalCausalMarkerGraph DA)
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u hun)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i v hvn)).val ↔
    LexEarlier (finiteCanonicalRankedRawGraph DA)
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u hun)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i v hvn)).val := by
  let R := finiteCanonicalRankedRawGraph DA
  let M := finiteCanonicalRankedOffBranchMask DA
  let m := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i s hsn)).val
  let a := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i u hun)).val
  let b := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i v hvn)).val
  have hma : m < a :=
    finiteCanonicalNodeAt_index_lt DA i s u hsu hun
  have hmb : m < b :=
    finiteCanonicalNodeAt_index_lt DA i s v hsv hvn
  have hRaw : R.oneMeetLevel a b = m :=
    finiteCanonicalRankedRaw_original_proper_oneMeet_exact
      DA i s u v hsn hsu hsv hun hvn hSourceMeet
  have hMask : SameEarlierMarkerMask M m a b :=
    finiteCanonicalRankedOffBranchMask_sharedSplit_below
      DA i i s u v (Or.inl hs) hsn rfl hsu hsv hun hvn hu hv
  have hNoMask : ∀ z : Nat, ¬ M m z := by
    intro z
    exact finiteCanonicalRankedOffBranchMask_split_middle_false
      DA i s (Or.inl hs) hsn z
  change LexEarlier (causalMarkerLimit R M) a b ↔ LexEarlier R a b
  exact causalMarkerLimit_original_lex_of_mask_prefix
    R M (finiteCanonicalRankedOffBranchMask_later DA)
    m a b hma hmb hRaw hMask hNoMask

end DiaryLeafPriority
end ThreeUniformDiaries
