import ThreeUniformDiaries.DiaryFiniteSignRootedRawVTwoCompatibility
import ThreeUniformDiaries.DiaryFiniteSignRootedPrefixCodes

/-!
# Actual V1 positive-parent compatibility at shared sign-rooted raw 1-splits

Suppose two genuine source flip branches i,j share their node at
a genuine one-split s. The node equality forces the SAME global
Devlin marker sign and all earlier genuine E3 witness bits.
The global sign fixes the ENTIRE E2 column: a leaf positive
at s in branch i is also positive there in branch j.

The verified prefix source-incidence theorem then identifies
that leaf's entire predecessor singleton code below s between
the two flips. V1 in branch j identifies it with any other
leaf positive at s in branch j. Finally raw cross-branch type
transport identifies the singleton edge tests against ALL earlier
raw nodes of the union, including offpath nodes.

Thus every two original positive raw E2 leaves at a shared
one-split are V1-compatible in the RAW amalgam, not merely
as corresponding source types.

This is a source-branch raw structural theorem only:
new off-branch Devlin edges can change singleton tests, so
the completed pre-diary V1/V3 and general absorber remain open.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace FiniteSignRootedFlipFamily

variable {A : Ordered3Graph Nat} {n : Nat} {ι : Type*}

/-- In the sign-rooted RAW tree, two positive E2 leaves from
branches sharing a genuine source one-split node s have
identical singleton predecessor types below s, tested against
EVERY earlier raw node. Both branches may otherwise differ
in later realised S2 bits. -/
theorem raw_shared_oneSplit_positive_parent_compatible
    (F : FiniteSignRootedFlipFamily A n ι)
    (i j : ι) (s : Nat)
    (hs : IsOneSplit A s)
    (hShared : F.node i s = F.node j s)
    (u v : Nat)
    (hsu : s < u) (hsv : s < v)
    (hun : u < n) (hvn : v < n)
    (hu : IsLeaf (F.graph i) u)
    (hv : IsLeaf (F.graph j) v)
    (hPosI : (F.graph i).edge 0 s u)
    (hPosJ : (F.graph j).edge 0 s v) :
    F.RawCrossOneTypeBelow s
      (F.node i u) (F.node j v) := by
  classical
  have hs3 : 3 ≤ s := hs.1
  have hsn : s < n := F.source.prediary.oneSplit_lt s hs
  have hSourcePair : FiniteSourceHasLeafPair A n := by
    obtain ⟨a,b,hab,hbn,ha,hb,hsa,hMeet⟩ :=
      finite_oneSplit_exists_ordered_leaf_witness F.source s hs
    exact ⟨(a,b),hab,hbn,ha,hb⟩
  let r := (finiteSourceLeafReference A n).1
  let t := (finiteSourceLeafReference A n).2
  obtain ⟨hrt,htn,hr,ht⟩ :=
    finiteSourceLeafReference_spec A n hSourcePair
  have hReference : (F.graph i).edge 1 r t ↔
      (F.graph j).edge 1 r t := by
    have hh := F.sign_eq_of_node_eq i j s hs3 hShared
    change decide ((F.graph i).edge 1 r t) =
      decide ((F.graph j).edge 1 r t) at hh
    by_cases hI : (F.graph i).edge 1 r t <;>
      by_cases hJ : (F.graph j).edge 1 r t <;> simp_all
  have hEarlierS2 :
      ∀ q : Nat, IsTwoSplit A q → q < s →
        ∃ a b c d : Nat,
          a < b ∧ c < d ∧ b < n ∧ d < n ∧
          IsLeaf A a ∧ IsLeaf A b ∧
          IsLeaf A c ∧ IsLeaf A d ∧
          q < a ∧ q < c ∧
          A.twoMeetLevel a b c d = q ∧
          ((F.graph i).edge q a b ↔
            (F.graph j).edge q a b) := by
    intro q hq hqs
    let idx : FiniteTwoSplitIndex A n :=
      ⟨⟨q,F.source.prediary.twoSplit_lt q hq⟩,hq⟩
    let W := finiteSelectedS2Witness F.source idx
    have hBit := F.s2_bit_eq_of_node_eq
      i j s hs3 hShared idx hqs
    have hDec :
        decide ((F.graph i).edge q W.a W.b) =
          decide ((F.graph j).edge q W.a W.b) := by
      change decide ((F.graph i).edge q W.a W.b) =
        decide ((F.graph j).edge q W.a W.b) at hBit
      exact hBit
    have hAgree : (F.graph i).edge q W.a W.b ↔
        (F.graph j).edge q W.a W.b := by
      by_cases hi : (F.graph i).edge q W.a W.b <;>
        by_cases hj : (F.graph j).edge q W.a W.b <;> simp_all
    exact ⟨W.a,W.b,W.c,W.d,W.hab,W.hcd,
      W.hbn,W.hdn,W.ha,W.hb,W.hc,W.hd,
      W.hsa,W.hsc,W.hMeet,hAgree⟩
  have hSourceU : IsLeaf A u :=
    ((F.flip i).role_iff u hu.1 hun).1.mpr hu
  have hTargetU : IsLeaf (F.graph j) u :=
    ((F.flip j).role_iff u hSourceU.1 hun).1.mp hSourceU
  have hJOne : IsOneSplit (F.graph j) s :=
    ((F.flip j).role_iff s hs.1 hsn).2.1.mp hs
  have hE2 :=
    finite_two_flips_E2_columns_equal_of_reference_marker
      (F.flip i) (F.flip j)
      r t hrt htn hr ht hReference
  have hPosJU : (F.graph j).edge 0 s u :=
    (hE2 s u hs hSourceU hsu hun).mp hPosI
  have hJSame : (F.graph j).SameOneTypeBelow s u v :=
    (F.flip j).target_diary.prediary.one_split_coherent
      s u v hJOne hTargetU hv hPosJU hPosJ
  have hJCode : oneCode (F.graph j) s u =
      oneCode (F.graph j) s v :=
    oneCode_eq_of_sameType (F.graph j) s u v hJSame
  have hPrefix := finite_two_flips_edges_agree_before_cut
    (F.flip i) (F.flip j) r t s
    hrt htn hr ht hReference hEarlierS2
  have hAcross : oneCode (F.graph i) s u =
      oneCode (F.graph j) s u :=
    finite_oneCode_eq_of_edge_prefix hPrefix
      u hsu.le hun
  exact F.rawCrossOneTypeBelow_of_source_codes
    i j s u v hShared hsu.le hsv.le hun hvn
    (hAcross.trans hJCode)

end FiniteSignRootedFlipFamily
end DiaryLeafPriority
end ThreeUniformDiaries
