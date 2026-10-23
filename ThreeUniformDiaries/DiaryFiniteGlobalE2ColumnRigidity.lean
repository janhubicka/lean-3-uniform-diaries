import ThreeUniformDiaries.DiaryFiniteGlobalDevlinOrientation
import ThreeUniformDiaries.DiaryFinitePositiveOneSplitAnchor
import ThreeUniformDiaries.DiaryFiniteFlipTransitivity

/-!
# One global Devlin sign determines every genuine E2 split column

A genuine finite diary flip preserves all leaf singleton meets. The
previously checked global Devlin theorem shows that all leaf-pair
marker-one orientation bits are either retained or reversed together.

Here V1 and the one-positive-witness E2 reconstruction extend each
orientation choice to EVERY E2 incidence at every one-split. In
particular, agreement at a SINGLE ordered leaf-pair marker-one
incidence implies that the whole E2 table of two flips agrees.
More generally, any two flips of a common source with the same
single reference marker-one bit have IDENTICAL E2 split columns.

CAUTION: A reversal does NOT simply complement E2 columns on ALL
later leaves. A leaf outside the original predecessor type cone has
no positive incidence with either orientation. Only the two
successor classes of the genuine split are exchanged; other
leaves stay negative. Thus this theorem is a uniqueness statement,
not a globally pointwise-complemented edge-table formula.

The E3 two-split columns are not controlled here; the existence
of arbitrary-source every-target-flip absorbers remains open.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- S1 provides an ordered pair of genuine leaves at each finite
one-split. The original split-witness interface does not order
its two leaves, so we do so here without changing its meet. -/
theorem finite_oneSplit_exists_ordered_leaf_witness
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (s : Nat) (hs : IsOneSplit A s) :
    ∃ a b : Nat, a < b ∧ b < n ∧
      IsLeaf A a ∧ IsLeaf A b ∧
      s < a ∧ A.oneMeetLevel a b = s := by
  classical
  obtain ⟨a,b,han,hbn,ha,hb,hsa,hsb,hMeet⟩ :=
    DA.prediary.one_split_witness s hs
      (DA.prediary.oneSplit_lt s hs)
  have hDistinct : a ≠ b := by
    intro hEq
    subst b
    have hBound : s + 1 ≤ min a a := by omega
    have hTooLate : s + 1 ≤ A.oneMeetLevel a a := by
      apply Nat.le_findGreatest hBound
      intro x y hxy hy
      exact Iff.rfl
    rw [hMeet] at hTooLate
    omega
  by_cases hab : a < b
  · exact ⟨a,b,hab,hbn,ha,hb,hsa,hMeet⟩
  · have hba : b < a := by omega
    refine ⟨b,a,hba,han,hb,ha,hsb,?_⟩
    rw [A.oneMeetLevel_comm b a]
    exact hMeet

/-- If all marker-one bits on ordered leaf pairs are preserved,
then every E2 incidence at a genuine one-split is preserved.
The proof uses a genuine S1 pair and propagates its (retained)
positive orientation to the entire column by V1 and the exact
numerical leaf meets. -/
theorem finite_flip_all_E2_columns_of_marker_one_preserved
    {A B : Ordered3Graph Nat} {n : Nat}
    (F : FiniteDiaryFlip A B n)
    (hMarker : ∀ a b : Nat, a < b → b < n →
      IsLeaf A a → IsLeaf A b →
      (A.edge 1 a b ↔ B.edge 1 a b)) :
    ∀ s u : Nat,
      IsOneSplit A s → IsLeaf A u → s < u → u < n →
      (A.edge 0 s u ↔ B.edge 0 s u) := by
  intro s u hs hu hsu hun
  obtain ⟨a,b,hab,hbn,ha,hb,hsa,hMeetA⟩ :=
    finite_oneSplit_exists_ordered_leaf_witness F.source_diary s hs
  have hsan : a < n := by omega
  have hsn : s < n := F.source_diary.prediary.oneSplit_lt s hs
  have hsB : IsOneSplit B s :=
    ((F.role_iff s hs.1 hsn).2.1).mp hs
  have haB : IsLeaf B a :=
    ((F.role_iff a ha.1 hsan).1).mp ha
  have hbB : IsLeaf B b :=
    ((F.role_iff b hb.1 hbn).1).mp hb
  have huB : IsLeaf B u :=
    ((F.role_iff u hu.1 hun).1).mp hu
  have hMeetB : B.oneMeetLevel a b = s :=
    (F.leaf_oneMeet a b hsan hbn ha hb).symm.trans hMeetA
  have hRight : A.edge 0 s b ↔ B.edge 0 s b := by
    have hA := finite_leaf_right_oneSplit_bit_iff_marker_one
      F.source_diary a b hab hbn ha hb
    have hB := finite_leaf_right_oneSplit_bit_iff_marker_one
      F.target_diary a b hab hbn haB hbB
    have hM := hMarker a b hab hbn ha hb
    simpa only [hMeetA,hMeetB] using
      (hA.symm.trans (hM.trans hB))
  have hOppA : ¬ (A.edge 0 s a ↔ A.edge 0 s b) :=
    E_oneSplit_distinguishing_zero_bit
      F.source_diary.prediary.permitted_edge
      s a b hs hab hsa hMeetA
  have hOppB : ¬ (B.edge 0 s a ↔ B.edge 0 s b) :=
    E_oneSplit_distinguishing_zero_bit
      F.target_diary.prediary.permitted_edge
      s a b hsB hab hsa hMeetB
  have hLeft : A.edge 0 s a ↔ B.edge 0 s a := by
    tauto
  by_cases hPosRight : A.edge 0 s b
  · have hBpos : B.edge 0 s b := hRight.mp hPosRight
    have hAcolumn :=
      finite_positive_oneSplit_edge_iff_later_oneMeet
        F.source_diary.prediary
        s b u hs hb hu (by omega) hsu hPosRight
    have hBcolumn :=
      finite_positive_oneSplit_edge_iff_later_oneMeet
        F.target_diary.prediary
        s b u hsB hbB huB (by omega) hsu hBpos
    have hMeet : A.oneMeetLevel b u = B.oneMeetLevel b u :=
      F.leaf_oneMeet b u hbn hun hb hu
    calc
      A.edge 0 s u ↔ s < A.oneMeetLevel b u := hAcolumn
      _ ↔ s < B.oneMeetLevel b u := by rw [hMeet]
      _ ↔ B.edge 0 s u := hBcolumn.symm
  · have hPosLeft : A.edge 0 s a := by
      by_contra hNegLeft
      exact hOppA (iff_of_false hNegLeft hPosRight)
    have hBpos : B.edge 0 s a := hLeft.mp hPosLeft
    have hAcolumn :=
      finite_positive_oneSplit_edge_iff_later_oneMeet
        F.source_diary.prediary
        s a u hs ha hu hsa hsu hPosLeft
    have hBcolumn :=
      finite_positive_oneSplit_edge_iff_later_oneMeet
        F.target_diary.prediary
        s a u hsB haB huB hsa hsu hBpos
    have hMeet : A.oneMeetLevel a u = B.oneMeetLevel a u :=
      F.leaf_oneMeet a u hsan hun ha hu
    calc
      A.edge 0 s u ↔ s < A.oneMeetLevel a u := hAcolumn
      _ ↔ s < B.oneMeetLevel a u := by rw [hMeet]
      _ ↔ B.edge 0 s u := hBcolumn.symm

/-- For a nontrivial finite leaf set, agreement of just ONE
reference marker-one bit between two genuine flips forces ALL
their E2 columns to agree. The full equality partition of
marker-one bits is a flip invariant, so the one reference bit
selects the globally preserved sign. -/
theorem finite_flip_all_E2_columns_of_one_reference_marker
    {A B : Ordered3Graph Nat} {n : Nat}
    (F : FiniteDiaryFlip A B n)
    (a b : Nat) (hab : a < b) (hbn : b < n)
    (ha : IsLeaf A a) (hb : IsLeaf A b)
    (hReference : A.edge 1 a b ↔ B.edge 1 a b) :
    ∀ s u : Nat,
      IsOneSplit A s → IsLeaf A u → s < u → u < n →
      (A.edge 0 s u ↔ B.edge 0 s u) := by
  rcases finite_flip_marker_one_global_sign F with hPres | hRev
  · exact finite_flip_all_E2_columns_of_marker_one_preserved
      F hPres
  · have hReverse := hRev a b hab hbn ha hb
    have : False := by tauto
    exact this.elim

/-- If two flips of a common finite source have the SAME
marker-one bit on one reference pair, then their COMPLETE E2
split columns agree, including both edges and nonedges for
all later leaf vertices. Thus a finite flip orbit has at most
two different E2 tables, classified by one global sign.
There is no assertion that both signs can always occur. -/
theorem finite_two_flips_E2_columns_equal_of_reference_marker
    {A B C : Ordered3Graph Nat} {n : Nat}
    (F : FiniteDiaryFlip A B n)
    (G : FiniteDiaryFlip A C n)
    (a b : Nat) (hab : a < b) (hbn : b < n)
    (ha : IsLeaf A a) (hb : IsLeaf A b)
    (hReference : B.edge 1 a b ↔ C.edge 1 a b) :
    ∀ s u : Nat,
      IsOneSplit A s → IsLeaf A u → s < u → u < n →
      (B.edge 0 s u ↔ C.edge 0 s u) := by
  let K : FiniteDiaryFlip B C n := F.symm.trans G
  have haB : IsLeaf B a :=
    ((F.role_iff a ha.1 (by omega)).1).mp ha
  have hbB : IsLeaf B b :=
    ((F.role_iff b hb.1 hbn).1).mp hb
  have hColumns := finite_flip_all_E2_columns_of_one_reference_marker
    K a b hab hbn haB hbB hReference
  intro s u hs hu hsu hun
  have hsn : s < n := F.source_diary.prediary.oneSplit_lt s hs
  have hsB : IsOneSplit B s :=
    ((F.role_iff s hs.1 hsn).2.1).mp hs
  have huB : IsLeaf B u :=
    ((F.role_iff u hu.1 hun).1).mp hu
  exact hColumns s u hsB huB hsu hun

end DiaryLeafPriority
end ThreeUniformDiaries
