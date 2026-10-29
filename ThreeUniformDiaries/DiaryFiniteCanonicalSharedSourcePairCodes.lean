import ThreeUniformDiaries.DiaryFiniteCanonicalFirstDifference
import ThreeUniformDiaries.DiaryFiniteSignRootedPrefixCodes
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalCrossTwoMeet

/-!
# Complete predecessor two-code equality at a shared real S2 cut

A shared sign-rooted split remembers the global Devlin sign and
every EARLIER selected S2 witness bit. This gives exact equality
of the entire source E1--E5 edge table at every first-coordinate
cut STRICTLY below that split (including nonedges), hence of
the full ordered pair-type codes of ANY ordered source pair
starting at or after the split.

We also record opposite E3 bits from a first-differing signature
coordinate on the SOURCE-FIXED S2 witness pair, without assuming
independent Boolean split orientations.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A SHARED true source 2-split node guarantees equality of
the complete predecessor source pair-code for all ordered
pairs at or above that split, even though the current E3
orientation may differ. This does not assume either pair is
positive at the split. -/
theorem finiteCanonicalSignRooted_source_twoCode_at_shared_split
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i j : FiniteCanonicalFlipIndex A n)
    (s : Nat) (hs : IsTwoSplit A s)
    (hShared :
      (finiteCanonicalSignRootedFamily DA).node i s =
      (finiteCanonicalSignRootedFamily DA).node j s)
    (u v : Nat) (hsu : s ≤ u) (huv : u < v)
    (hvn : v < n) :
    twoCode ((finiteCanonicalSignRootedFamily DA).graph i) s u v =
      twoCode ((finiteCanonicalSignRootedFamily DA).graph j) s u v := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  have hs3 : 3 ≤ s := hs.1
  have hsn : s < n := DA.prediary.twoSplit_lt s hs
  have hHasPair : FiniteSourceHasLeafPair A n := by
    obtain ⟨a,b,c,d,hab,hcd,han,hbn,hcn,hdn,
      ha,hb,hc,hd,hsa,hsc,hMeet⟩ :=
        DA.prediary.two_split_witness s hs hsn
    exact ⟨(a,b),hab,hbn,ha,hb⟩
  let r := (finiteSourceLeafReference A n).1
  let t := (finiteSourceLeafReference A n).2
  obtain ⟨hrt,htn,hr,ht⟩ :=
    finiteSourceLeafReference_spec A n hHasPair
  have hReference : (F.graph i).edge 1 r t ↔
      (F.graph j).edge 1 r t := by
    have hb := F.sign_eq_of_node_eq i j s hs3 hShared
    change decide ((F.graph i).edge 1 r t) =
      decide ((F.graph j).edge 1 r t) at hb
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
      ⟨⟨q,DA.prediary.twoSplit_lt q hq⟩,hq⟩
    let W := finiteSelectedS2Witness DA idx
    have hb := F.s2_bit_eq_of_node_eq
      i j s hs3 hShared idx hqs
    have hSame :
        (F.graph i).edge q W.a W.b ↔
        (F.graph j).edge q W.a W.b := by
      change decide ((F.graph i).edge q W.a W.b) =
        decide ((F.graph j).edge q W.a W.b) at hb
      by_cases hi : (F.graph i).edge q W.a W.b <;>
        by_cases hj : (F.graph j).edge q W.a W.b <;> simp_all
    exact ⟨W.a,W.b,W.c,W.d,
      W.hab,W.hcd,W.hbn,W.hdn,
      W.ha,W.hb,W.hc,W.hd,W.hsa,W.hsc,W.hMeet,hSame⟩
  have hPrefix : ∀ x y z : Nat,
      x < y → y < z → z < n → x < s →
      ((F.graph i).edge x y z ↔ (F.graph j).edge x y z) :=
    finite_two_flips_edges_agree_before_cut
      (F.flip i) (F.flip j)
      r t s hrt htn hr ht hReference hEarlier
  exact finite_twoCode_eq_of_edge_prefix hPrefix
    u v hsu huv hvn

/-- Differing selected E3 signature bits at one genuine
two-split mean the literal positive-edge incidences on the
SAME source-fixed ordered witness pair are opposite. -/
theorem finiteCanonicalSignRooted_selected_pair_E3_different
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i j : FiniteCanonicalFlipIndex A n)
    (s : FiniteTwoSplitIndex A n)
    (hDiff :
      ((finiteCanonicalSignRootedFamily DA).signature i).2 s ≠
      ((finiteCanonicalSignRootedFamily DA).signature j).2 s) :
    let W := finiteSelectedS2Witness DA s
    ¬ (((finiteCanonicalSignRootedFamily DA).graph i).edge
        s.val.val W.a W.b ↔
       ((finiteCanonicalSignRootedFamily DA).graph j).edge
        s.val.val W.a W.b) := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let W := finiteSelectedS2Witness DA s
  change decide ((F.graph i).edge s.val.val W.a W.b) ≠
    decide ((F.graph j).edge s.val.val W.a W.b) at hDiff
  dsimp only
  by_cases hi : (F.graph i).edge s.val.val W.a W.b <;>
    by_cases hj : (F.graph j).edge s.val.val W.a W.b <;> simp_all

end DiaryLeafPriority
end ThreeUniformDiaries
