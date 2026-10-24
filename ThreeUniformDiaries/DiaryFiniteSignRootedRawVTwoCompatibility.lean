import ThreeUniformDiaries.DiaryFiniteSignRootedRawCrossType
import ThreeUniformDiaries.DiaryFiniteSignRootedVTwoParentCompatibility

/-!
# Actual V2 positive-parent compatibility at shared sign-rooted raw splits

The verified source theorem states that two genuine finite flips
sharing the global Devlin sign and all earlier S2 witness bits
have matching full positive pair-type parent codes at a 2-split s,
even when their E3 successor orientations at s differ.

A sign-rooted raw node at source level s encodes EXACTLY the
same earlier sign and S2 data. Its equality between two branches
provides all source assumptions. The separate cross-branch RAW
type transport theorem upgrades equality of the SOURCE parent
codes to equality of their actual raw predecessor tests against
EVERY earlier raw node, including off-path vertices.

Hence two positive E3 witness pairs on two possibly distinct
branches sharing a node at s are V2-compatible in the raw union.
This is the full RAW cross-branch V2 positive-class condition at
the shared node, rather than just source-side agreement.

IMPORTANT: adding new cross-branch Devlin marker edges may change
these type tests. This theorem does NOT construct the required
cross-branch marker completion, prove V3, preserve all mixed
numerical meets, or give a general absorber.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace FiniteSignRootedFlipFamily

variable {A : Ordered3Graph Nat} {n : Nat} {ι : Type*}

/-- Every shared genuine source 2-split node has a single RAW
positive predecessor full pair-type profile across arbitrary
branches, independently of the two current E3 orientations.

All tests at earlier source levels range over the ENTIRE raw
sign-rooted amalgam. The source leaf witnesses are explicitly
positive in the respective original branches. -/
theorem raw_shared_twoSplit_positive_parent_compatible
    (F : FiniteSignRootedFlipFamily A n ι)
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
    F.RawCrossTwoTypeBelow s
      (F.node i u) (F.node i v)
      (F.node j w) (F.node j z) := by
  classical
  have hsn : s < n := F.source.prediary.twoSplit_lt s hs
  have hs3 : 3 ≤ s := hs.1
  have hSourcePair : FiniteSourceHasLeafPair A n := by
    obtain ⟨a,b,c,d,hab,hcd,_han,hbn,_hcn,hdn,
      ha,hb,hc,hd,hsa,hsc,hMeet⟩ :=
      F.source.prediary.two_split_witness s hs hsn
    exact ⟨(a,b),hab,hbn,ha,hb⟩
  let r := (finiteSourceLeafReference A n).1
  let t := (finiteSourceLeafReference A n).2
  obtain ⟨hrt,htn,hr,ht⟩ :=
    finiteSourceLeafReference_spec A n hSourcePair
  have hSign : (F.graph i).edge 1 r t ↔
      (F.graph j).edge 1 r t := by
    have hBitEq := F.sign_eq_of_node_eq i j s hs3 hShared
    change decide ((F.graph i).edge 1 r t) =
      decide ((F.graph j).edge 1 r t) at hBitEq
    by_cases hi : (F.graph i).edge 1 r t <;>
      by_cases hj : (F.graph j).edge 1 r t <;> simp_all
  have hEarlier :
      ∀ q : Nat, IsTwoSplit A q → q < s →
        ∃ a b c d : Nat,
          a < b ∧ c < d ∧ b < n ∧ d < n ∧
          IsLeaf A a ∧ IsLeaf A b ∧
          IsLeaf A c ∧ IsLeaf A d ∧
          q < a ∧ q < c ∧
          A.twoMeetLevel a b c d = q ∧
          ((F.graph i).edge q a b ↔ (F.graph j).edge q a b) := by
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
    exact ⟨W.a,W.b,W.c,W.d,
      W.hab,W.hcd,W.hbn,W.hdn,
      W.ha,W.hb,W.hc,W.hd,W.hsa,W.hsc,W.hMeet,hAgree⟩
  let index : FiniteTwoSplitIndex A n := ⟨⟨s,hsn⟩,hs⟩
  let W := finiteSelectedS2Witness F.source index
  have hParentSource :
      twoCode (F.graph i) s u v =
        twoCode (F.graph j) s w z :=
    finite_signRooted_positive_twoSplit_parent_codes_agree
      (F.flip i) (F.flip j)
      r t s hrt htn hr ht hs hSign hEarlier
      W.a W.b W.c W.d
      W.hab W.hcd W.hbn W.hdn
      W.ha W.hb W.hc W.hd W.hsa W.hsc W.hMeet
      u v w z huv hwz hu hv hw hz hPosI hPosJ
  exact F.rawCrossTwoTypeBelow_of_source_codes
    i j s u v w z hShared
    hsu.le hsw.le huv hwz hvn hzn hParentSource

end FiniteSignRootedFlipFamily
end DiaryLeafPriority
end ThreeUniformDiaries
