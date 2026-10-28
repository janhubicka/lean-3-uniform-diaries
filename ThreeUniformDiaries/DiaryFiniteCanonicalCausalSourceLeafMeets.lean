import ThreeUniformDiaries.DiaryFiniteCanonicalCausalMarkerOnePairMeet
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalCommonFirstCap
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalOriginalTwoMeet
import ThreeUniformDiaries.DiaryFiniteBlockProtectedS2

/-!
# All original leaf-pair two-meets survive the causal sign-rooted completion

The EXACT finite manuscript S2 trichotomy says that the full meet
of two ordered pairs of leaves in a genuine finite source diary
is either:
  (i) the Devlin marker 1;
  (ii) an actual 2-split;
  (iii) the common first leaf of the two pairs.

The preceding independent Lean proofs verify that the actual
Nat-indexed causal sign-rooted graph preserves each of these cases,
including all off-path predecessor vertices and same-level ties.
The marker-one case uses its first differing Devlin bit. The 2-split
case uses the opposing old E3 bits. The capped case uses the
same-branch mask theorem at an arbitrary leaf rank cut.

This module combines the three cases into a SINGLE exact numerical
full twoMeetLevel transport theorem for every original source-flip
branch and ALL its ordered leaf pairs, with no assumed output S2.

Together with the existing exact singleton meets, this is the
protected S1/S2 picture prerequisite for relative completion.
It does not yet prove mixed split-containing meets are preserved
by the causal raw gluing or that every target flip is absorbed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every full ordered-pair meet of genuine source leaves is
preserved as the exact numerical RANK of its original source
meet, including marker 1, genuine 2-splits and a common first
leaf cap. This does not assume the completed finite graph is
already a full diary. -/
theorem finiteCanonicalCausalMarkerGraph_original_leaf_twoMeets_exact
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (hbn : b < n) (hdn : d < n)
    (ha : IsLeaf A a) (hb : IsLeaf A b)
    (hc : IsLeaf A c) (hd : IsLeaf A d) :
    (finiteCanonicalCausalMarkerGraph DA).twoMeetLevel
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i a (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i b hbn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i c (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i d hdn)).val =
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i
          (((finiteCanonicalSignRootedFamily DA).graph i).twoMeetLevel
            a b c d) (by omega))).val := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let G := finiteCanonicalCausalMarkerGraph DA
  have han : a < n := by omega
  have hcn : c < n := by omega
  have hFa : IsLeaf (F.graph i) a :=
    ((F.flip i).role_iff a ha.1 han).1.mp ha
  have hFb : IsLeaf (F.graph i) b :=
    ((F.flip i).role_iff b hb.1 hbn).1.mp hb
  have hFc : IsLeaf (F.graph i) c :=
    ((F.flip i).role_iff c hc.1 hcn).1.mp hc
  have hFd : IsLeaf (F.graph i) d :=
    ((F.flip i).role_iff d hd.1 hdn).1.mp hd
  let m := (F.graph i).twoMeetLevel a b c d
  have hmBound : m < n := by
    have h := (F.graph i).twoMeetLevel_le_min a b c d
    dsimp [m]
    omega
  have hCase := finiteRoleDiary_pair_meets_exact
    (F.flip i).target_diary
    a b c d hab hcd hbn hdn hFa hFb hFc hFd
  rcases hCase with hMarker | hSplit | ⟨hac,hCap⟩
  · have hTarget : G.twoMeetLevel
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i a han)).val
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i b hbn)).val
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i c hcn)).val
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i d hdn)).val = 1 :=
      finiteCanonicalCausalMarkerGraph_original_markerOne_twoMeet_exact
        DA i a b c d hab hcd hbn hdn ha hb hc hd hMarker
    have hMarkerRank : (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i 1 (by
          have hn := DA.prediary.frame.length_ge_three
          omega))).val = 1 :=
      finiteCanonicalMarker_one_rank DA i
    change G.twoMeetLevel
        (finiteCanonicalNodeIndex DA (finiteCanonicalNodeAt DA i a han)).val
        (finiteCanonicalNodeIndex DA (finiteCanonicalNodeAt DA i b hbn)).val
        (finiteCanonicalNodeIndex DA (finiteCanonicalNodeAt DA i c hcn)).val
        (finiteCanonicalNodeIndex DA (finiteCanonicalNodeAt DA i d hdn)).val =
      (finiteCanonicalNodeIndex DA (finiteCanonicalNodeAt DA i m hmBound)).val
    rw [show m = 1 from hMarker]
    exact hTarget.trans hMarkerRank.symm
  · have hmn : m < n := hmBound
    have hmA : IsTwoSplit A m :=
      ((F.flip i).role_iff m hSplit.1 hmn).2.2.mpr hSplit
    have hma : m < a := by
      have hcap := (F.graph i).twoMeetLevel_le_min a b c d
      have hne : m ≠ a := by
        intro heq
        have hx : IsTwoSplit (F.graph i) a := by
          simpa only [heq] using hSplit
        exact hFa.2.2 hx.2.2
      dsimp [m]
      omega
    have hmc : m < c := by
      have hcap := (F.graph i).twoMeetLevel_le_min a b c d
      have hne : m ≠ c := by
        intro heq
        have hx : IsTwoSplit (F.graph i) c := by
          simpa only [heq] using hSplit
        exact hFc.2.2 hx.2.2
      dsimp [m]
      omega
    exact finiteCanonicalCausalMarkerGraph_original_twoMeet_exact_at_twoSplit
      DA i m a b c d hmA hmn hma hmc
      hab hcd hbn hdn ha hb hc hd rfl
  · subst c
    have h := finiteCanonicalCausalMarkerGraph_original_commonFirst_twoMeet_exact
      DA i a b d hab hcd hbn hdn hb hd hCap
    change G.twoMeetLevel
        (finiteCanonicalNodeIndex DA (finiteCanonicalNodeAt DA i a han)).val
        (finiteCanonicalNodeIndex DA (finiteCanonicalNodeAt DA i b hbn)).val
        (finiteCanonicalNodeIndex DA (finiteCanonicalNodeAt DA i a han)).val
        (finiteCanonicalNodeIndex DA (finiteCanonicalNodeAt DA i d hdn)).val =
      (finiteCanonicalNodeIndex DA (finiteCanonicalNodeAt DA i m hmBound)).val
    rw [show m = a from hCap]
    exact h

end DiaryLeafPriority
end ThreeUniformDiaries
