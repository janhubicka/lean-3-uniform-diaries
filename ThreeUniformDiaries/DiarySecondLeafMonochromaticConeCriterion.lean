import ThreeUniformDiaries.DiarySecondLeafFixedCandidateConverse
import ThreeUniformDiaries.DiaryOneOldCutColourAllNewMeets
import ThreeUniformDiaries.DiaryFirstLeafInjectiveRange
import ThreeUniformDiaries.DiarySecondLeafFavourableSplitCriterion

/-!
# Track A: an actual monochromatic infinite cone is good at the second leaf
# precisely when its fixed root split passes three finite tests

Fix an actual old reserved diary stage P containing exactly one
selected source leaf a, whose fixed target image is f(a). The next
true source diary leaf is m>a.

Let J:Nat→Nat be ANY injective family of actual target true leaves
from the ORIGINAL prescribed F-range, all strictly later than f(a)
and all of the SAME complete mixed singleton colour below B>f(a).
This includes every genuine homogeneous induced generic leaf cone,
but no genericity hypothesis is needed for the local argument.

The exact singleton colour-meet invariance theorem says that the
NUMERICAL S1 meet s=oneMeet_K(f(a),J(0)) is the SAME s for ALL J(t).
The full target V1 axiom then forces the new leaf's right E2 bit
to be the complement of the fixed root's bit at s.

Using the verified complete six-vertex second-leaf successor iff,
there are arbitrarily numerically late ACTUAL reserved successors
whose new image belongs to this SAME J range if and only if:
  (1) the source right E2 bit matches that target complement;
  (2) the source singleton meet level is at most s;
  (3) the old source gap from its meet to a fits into the target
      gap between s and the fixed old image f(a).

The final gap f(a)+(m-a)≤J(t) can always be satisfied by choosing
a sufficiently late vertex of the injective J range.

This is an EXPLICIT necessary-and-sufficient finite anchor test
for each actual monochromatic second-leaf cone, not merely an
existential all-or-none dichotomy. It does NOT prove an arbitrary
generic colour cone passes these tests or that any one chosen
next leaf persists through all later source horizons.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Exact source/target E2 sign and two gap test for unbounded
genuine reserved SECOND-source-leaf successors in one fixed
injective monochromatic target leaf cone J.

All old source images are fixed literally by the reserved
successor; target J may have arbitrary numerical enumeration
order, but all its values are > f(a). If J is induced generic,
this applies without using its internal E5 graph structure. -/
theorem RoleDiary.second_leaf_fixed_colour_cone_good_iff_favourable_split
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (F f J : Nat → Nat) (a m B : Nat)
    (ha : IsLeaf H a) (hm : IsLeaf H m) (ham : a < m)
    (hOld : countableDiaryLeafPrefix H m = {a})
    (P : ReservedDiaryStage H K F m f)
    (hJInj : Function.Injective J)
    (hJLeaf : ∀ t : Nat, IsLeaf K (J t))
    (hJRange : ∀ t : Nat, ∃ i : Nat, J t = F i)
    (hCut : f a < B)
    (hJAbove : ∀ t : Nat, f a < J t)
    (hMono : ∀ t : Nat,
      DiaryLowerBoundColors.singletonColour K B (J t) =
        DiaryLowerBoundColors.singletonColour K B (J 0)) :
    let s := K.oneMeetLevel (f a) (J 0)
    ((H.edge 0 (H.oneMeetLevel a m) m ↔
          ¬ K.edge 0 s (f a)) ∧
      H.oneMeetLevel a m ≤ s ∧
      s + (a - H.oneMeetLevel a m) ≤ f a) ↔
    (∀ M : Nat, ∃ t : Nat,
      M < J t ∧
      ∃ g : Nat → Nat,
        ReservedDiaryStage H K F (m + 1) g ∧
        (∀ x : Nat, x ∈ countableDiaryLeafPrefix H m →
          g x = f x) ∧
        g m = J t) := by
  classical
  let s := K.oneMeetLevel (f a) (J 0)
  have haPrefix : a ∈ countableDiaryLeafPrefix H m := by
    rw [hOld]
    simp
  have haSupport : a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) a haPrefix
  have hRootLeaf : IsLeaf K (f a) :=
    P.1.leaf_role a haSupport ha
  have hSRole : IsOneSplit K s :=
    DK.singleton_meets (f a) (J 0) hRootLeaf
      (hJLeaf 0) (ne_of_lt (hJAbove 0))
  have hSBelow : s < f a :=
    DK.oneMeet_lt_left_of_distinct_leaves
      (f a) (J 0) hRootLeaf (hJLeaf 0)
      (ne_of_lt (hJAbove 0))
  have hMeet (t : Nat) :
      K.oneMeetLevel (f a) (J t) = s := by
    have hColour :
        DiaryLowerBoundColors.singletonColour K B (J 0) =
        DiaryLowerBoundColors.singletonColour K B (J t) :=
      (hMono t).symm
    exact (same_complete_singletonColour_fixes_all_oneNew_meets
      K B (f a) (f a) (f a) (J 0) (J t)
      hCut hCut (hJAbove 0) (hJAbove t) hColour).1.symm
  have hE2 (t : Nat) :
      (K.edge 0 s (J t) ↔ ¬ K.edge 0 s (f a)) := by
    have hOpp :
        ¬ (K.edge 0 s (f a) ↔ K.edge 0 s (J t)) :=
      DK.oneSplit_witness_opposite_marker
        s (f a) (J t) hSRole hRootLeaf (hJLeaf t)
        hSBelow (lt_trans hSBelow (hJAbove t)) (hMeet t)
    tauto
  constructor
  · rintro ⟨hBit, hGap1, hGap2⟩ M
    obtain ⟨t, htHigh⟩ :=
      exists_ge_of_injective_nat J hJInj
        (max (M + 1) (f a + (m - a)))
    have hHigh : M < J t := by omega
    have hGap3 : f a + (m - a) ≤ J t := by omega
    have hTargetBit :
        (H.edge 0 (H.oneMeetLevel a m) m ↔
          K.edge 0 (K.oneMeetLevel (f a) (J t)) (J t)) := by
      rw [hMeet t]
      exact hBit.trans (hE2 t).symm
    have hTargetGap1 :
        H.oneMeetLevel a m ≤ K.oneMeetLevel (f a) (J t) := by
      rw [hMeet t]
      exact hGap1
    have hTargetGap2 :
        K.oneMeetLevel (f a) (J t) +
          (a - H.oneMeetLevel a m) ≤ f a := by
      rw [hMeet t]
      exact hGap2
    obtain ⟨g, Q, hOldImages, hNewImage⟩ :=
      (DH.second_leaf_fixed_v_reserved_successor_iff
        DK F f a m (J t)
        ha hm ham hOld P (hJLeaf t) (hJRange t)).mpr
          ⟨hTargetBit,hTargetGap1,hTargetGap2,hGap3⟩
    exact ⟨t,hHigh,g,Q,hOldImages,hNewImage⟩
  · intro hCofinal
    obtain ⟨t, _htHigh, g, Q, hOldImages, hNewImage⟩ :=
      hCofinal 0
    obtain ⟨hTargetBit,hGap1,hGap2,_hGap3⟩ :=
      (DH.second_leaf_fixed_v_reserved_successor_iff
        DK F f a m (J t)
        ha hm ham hOld P (hJLeaf t) (hJRange t)).mp
          ⟨g,Q,hOldImages,hNewImage⟩
    have hBit :
        (H.edge 0 (H.oneMeetLevel a m) m ↔
          ¬ K.edge 0 s (f a)) := by
      calc
        H.edge 0 (H.oneMeetLevel a m) m ↔
            K.edge 0 (K.oneMeetLevel (f a) (J t)) (J t) :=
          hTargetBit
        _ ↔ K.edge 0 s (J t) := by rw [hMeet t]
        _ ↔ ¬ K.edge 0 s (f a) := hE2 t
    rw [hMeet t] at hGap1 hGap2
    exact ⟨hBit,hGap1,hGap2⟩

end DiaryLeafPriority
end ThreeUniformDiaries
