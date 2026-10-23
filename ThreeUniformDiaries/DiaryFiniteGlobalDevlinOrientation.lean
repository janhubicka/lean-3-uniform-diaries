import ThreeUniformDiaries.DiaryFinitePairMeetCoupledOneSplit
import ThreeUniformDiaries.DiaryFiniteAlternatingRequiresTwoSplit
import ThreeUniformDiaries.DiaryFiniteFlipFirstDirection

/-!
# One global Devlin marker-one orientation sign in finite diary flips

The full two-type meet of any two ordered leaf pairs is greater than
marker level 1 precisely when their marker-one auxiliary bits agree.
The reverse implication uses only the E1--E5 permitted edge shapes,
the fact that all genuine leaves have the same type below cut 2, and
the literal definition of the full meet. No independent split controls
and no false mixed-pair transfer are invoked.

Since a genuine flip preserves ALL numerical full two-type meets of
ordered LEAF pairs, it preserves the equality partition of marker-one
bits. Hence the complete marker-one pattern in a target flip is
either exactly the source pattern or its pointwise complement, with a
single global choice.

This is a necessary restriction on genuine flips, not a construction
of a finite absorber for arbitrary source diaries.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Any two leaves have the same singleton type at all tests below
cut 2: the only possible test is the absent leaf-role edge (0,1,z). -/
theorem finite_leaves_same_oneType_below_two
    {H : Ordered3Graph Nat}
    {a c : Nat}
    (ha : IsLeaf H a) (hc : IsLeaf H c) :
    H.SameOneTypeBelow 2 a c := by
  intro x y hxy hy
  have h0 : x = 0 ∧ y = 1 := by omega
  obtain ⟨rfl,rfl⟩ := h0
  exact iff_of_false ha.2.1 hc.2.1

/-- Marker-one agreement characterises the full pair-type-meet cut.
For ordered LEAF pairs the converse of the standard meet-agreement
lemma holds already in a finite pre-diary: at cut 2 the two singleton
coordinate types agree by the common leaf role, and the auxiliary
marker-zero test is absent by E1--E5, leaving only marker one. -/
theorem finite_leaf_pair_meet_gt_one_iff_marker_one_agree
    {H : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRolePrediaryBlock H n)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (hbn : b < n) (hdn : d < n)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d) :
    (1 < H.twoMeetLevel a b c d) ↔
      (H.edge 1 a b ↔ H.edge 1 c d) := by
  classical
  have ha3 : 3 ≤ a := ha.1
  have hc3 : 3 ≤ c := hc.1
  constructor
  · intro hMeet
    exact (H.twoMeetLevel_agree a b c d).2.2 hMeet
  · intro hMark
    have hSame : H.SameTwoTypeBelow 2 a b c d := by
      refine ⟨finite_leaves_same_oneType_below_two ha hc,
        finite_leaves_same_oneType_below_two hb hd, ?_⟩
      intro x hx
      have hx01 : x = 0 ∨ x = 1 := by omega
      rcases hx01 with rfl | rfl
      · exact iff_of_false
          (finite_leaf_middle_no_zero_edge D a b ha)
          (finite_leaf_middle_no_zero_edge D c d hc)
      · exact hMark
    have hTwo : 2 ≤ H.twoMeetLevel a b c d := by
      apply Nat.le_findGreatest
        (show 2 ≤ min a c by omega)
      exact hSame
    omega

/-- A genuine finite flip preserves not merely each leaf-pair full
meet but the complete equality relation between all Devlin
marker-one incidences on ordered leaf pairs. -/
theorem finite_flip_preserves_marker_one_equality
    {A B : Ordered3Graph Nat} {n : Nat}
    (F : FiniteDiaryFlip A B n)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (hbn : b < n) (hdn : d < n)
    (ha : IsLeaf A a) (hb : IsLeaf A b)
    (hc : IsLeaf A c) (hd : IsLeaf A d) :
    (A.edge 1 a b ↔ A.edge 1 c d) ↔
      (B.edge 1 a b ↔ B.edge 1 c d) := by
  have haB : IsLeaf B a :=
    ((F.role_iff a ha.1 (by omega)).1).mp ha
  have hbB : IsLeaf B b :=
    ((F.role_iff b hb.1 hbn).1).mp hb
  have hcB : IsLeaf B c :=
    ((F.role_iff c hc.1 (by omega)).1).mp hc
  have hdB : IsLeaf B d :=
    ((F.role_iff d hd.1 hdn).1).mp hd
  have hA := finite_leaf_pair_meet_gt_one_iff_marker_one_agree
    F.source_diary.prediary a b c d
    hab hcd hbn hdn ha hb hc hd
  have hB := finite_leaf_pair_meet_gt_one_iff_marker_one_agree
    F.target_diary.prediary a b c d
    hab hcd hbn hdn haB hbB hcB hdB
  have hMeet := F.leaf_twoMeet
    a b c d hab hcd hbn hdn ha hb hc hd
  constructor
  · intro h
    apply hB.mp
    rw [← hMeet]
    exact hA.mpr h
  · intro h
    apply hA.mp
    rw [hMeet]
    exact hB.mpr h

/-- In any finite diary flip the full array of marker-one bits on
ordered leaf pairs is either UNCHANGED or GLOBALLY COMPLEMENTED.
There is one sign for all pairs, including pairs crossing distinct
one-splits. No reference pair is required in the statement; if
there are no ordered pairs of leaves the first case is vacuous. -/
theorem finite_flip_marker_one_global_sign
    {A B : Ordered3Graph Nat} {n : Nat}
    (F : FiniteDiaryFlip A B n) :
    (∀ a b : Nat, a < b → b < n →
      IsLeaf A a → IsLeaf A b →
        (A.edge 1 a b ↔ B.edge 1 a b)) ∨
    (∀ a b : Nat, a < b → b < n →
      IsLeaf A a → IsLeaf A b →
        (A.edge 1 a b ↔ ¬ B.edge 1 a b)) := by
  classical
  by_cases hex :
      ∃ a₀ b₀ : Nat, a₀ < b₀ ∧ b₀ < n ∧
        IsLeaf A a₀ ∧ IsLeaf A b₀
  · obtain ⟨a₀,b₀,hab₀,hbn₀,ha₀,hb₀⟩ := hex
    by_cases hRef : (A.edge 1 a₀ b₀ ↔ B.edge 1 a₀ b₀)
    · left
      intro a b hab hbn ha hb
      have hRelative := finite_flip_preserves_marker_one_equality
        F a b a₀ b₀ hab hab₀ hbn hbn₀ ha hb ha₀ hb₀
      tauto
    · right
      intro a b hab hbn ha hb
      have hRelative := finite_flip_preserves_marker_one_equality
        F a b a₀ b₀ hab hab₀ hbn hbn₀ ha hb ha₀ hb₀
      tauto
  · left
    intro a b hab hbn ha hb
    exact False.elim (hex ⟨a,b,hab,hbn,ha,hb⟩)

end DiaryLeafPriority
end ThreeUniformDiaries
