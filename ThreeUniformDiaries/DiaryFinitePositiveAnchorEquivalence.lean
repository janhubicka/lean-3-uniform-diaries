import ThreeUniformDiaries.DiaryFinitePositiveAnchorCompletion

/-!
# Exact positive-anchor criterion for a bounded finite leaf preembedding

The source V/E/S diary axioms supply at least one positive
E2-incidence at every genuine one-split and one positive E3
ordered leaf pair at every genuine two-split. This follows
from the preserved exact singleton/full pair type meets of
the split witnesses, not from independent Boolean controls.

For a fixed finite leaf preembedding Q, the Lean-verified
positive-anchor completion theorem is not merely sufficient:
its anchor hypotheses are also NECESSARY whenever Q's map
is a fully induced, mixed-meet preserving embedding.

Thus completing an existing bounded leaf preembedding amounts
EXACTLY to orienting one genuine positive witness at each source
split correctly. The still-open general finite flip absorption
problem is to construct a target with suitable coherent choices
for every target flip.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every genuine one-split in a finite full diary has a leaf
which is positively incident with its E2 column.
Otherwise both S1 witness leaves would have identical
singleton types THROUGH the first-disagreement cut. -/
theorem finite_oneSplit_exists_positive_anchor
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (s : Nat) (hs : IsOneSplit A s) :
    ∃ a : Nat, IsLeaf A a ∧ s < a ∧ a < n ∧
      A.edge 0 s a := by
  classical
  obtain ⟨a,b,han,hbn,ha,hb,hsa,hsb,hMeet⟩ :=
    DA.prediary.one_split_witness s hs
      (DA.prediary.oneSplit_lt s hs)
  by_cases hPa : A.edge 0 s a
  · exact ⟨a,ha,hsa,han,hPa⟩
  by_cases hPb : A.edge 0 s b
  · exact ⟨b,hb,hsb,hbn,hPb⟩
  have hBelow : A.SameOneTypeBelow s a b := by
    rw [←hMeet]
    exact A.oneMeetLevel_agree a b
  have hNext : A.SameOneTypeBelow (s+1) a b := by
    intro x y hxy hy
    by_cases hys : y < s
    · exact hBelow hxy hys
    · have hyEq : y = s := by omega
      subst y
      by_cases hx0 : x = 0
      · subst x
        exact iff_of_false hPa hPb
      · have hxPos : 0 < x := by omega
        exact iff_of_false
          (E_oneSplit_no_positive_aux
            DA.prediary.permitted_edge s x a hs hxPos)
          (E_oneSplit_no_positive_aux
            DA.prediary.permitted_edge s x b hs hxPos)
  have hBound : s+1 ≤ min a b := by omega
  have hTooLarge : s+1 ≤ A.oneMeetLevel a b :=
    Nat.le_findGreatest hBound hNext
  rw [hMeet] at hTooLarge
  omega

/-- Every genuine two-split in a finite full diary has a
positive ordered leaf pair in its E3 column. An exact S2
witness pair of pair-types has opposite E3 incidences. -/
theorem finite_twoSplit_exists_positive_anchor
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (s : Nat) (hs : IsTwoSplit A s) :
    ∃ a b : Nat, a < b ∧ b < n ∧
      IsLeaf A a ∧ IsLeaf A b ∧ s < a ∧
      A.edge s a b := by
  obtain ⟨a,b,c,d,hab,hcd,han,hbn,hcn,hdn,
    ha,hb,hc,hd,hsa,hsc,hMeet⟩ :=
    DA.prediary.two_split_witness s hs
      (DA.prediary.twoSplit_lt s hs)
  have hDiff : ¬ (A.edge s a b ↔ A.edge s c d) :=
    E_twoSplit_pair_aux_distinguishes
      DA.prediary.permitted_edge s a b c d hs hsa hsc hMeet
  by_cases hPosAB : A.edge s a b
  · exact ⟨a,b,hab,hbn,ha,hb,hsa,hPosAB⟩
  · have hPosCD : A.edge s c d := by
      by_contra hNegCD
      exact hDiff (iff_of_false hPosAB hNegCD)
    exact ⟨c,d,hcd,hdn,hc,hd,hsc,hPosCD⟩

/-- For fixed genuine finite diaries A,B and a fixed bounded
leaf preembedding Q, ONE correctly mapped positive anchor
per source 1-split and 2-split is NECESSARY AND SUFFICIENT
for Q's map to be a fully induced/all-numerical-meet
embedding. The source has such anchors by S1/S2; existence
of a coherent target selection is not asserted. -/
theorem finite_leafPreembedding_boundedEmbedding_iff_positive_anchors
    {A B : Ordered3Graph Nat} {n k : Nat}
    {f : Nat → Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (DB : FiniteRoleDiaryBlock B k)
    (Q : FiniteLeafPreembedding A B n k f) :
    FiniteBoundedMeetEmbedding A B n k f ↔
      (∀ s : Nat, IsOneSplit A s →
        ∃ a : Nat, IsLeaf A a ∧ s < a ∧ a < n ∧
          A.edge 0 s a ∧ B.edge 0 (f s) (f a)) ∧
      (∀ s : Nat, IsTwoSplit A s →
        ∃ a b : Nat, a < b ∧ b < n ∧
          IsLeaf A a ∧ IsLeaf A b ∧ s < a ∧
          A.edge s a b ∧ B.edge (f s) (f a) (f b)) := by
  constructor
  · intro E
    constructor
    · intro s hs
      obtain ⟨a,ha,hsa,han,hPosA⟩ :=
        finite_oneSplit_exists_positive_anchor DA s hs
      have h0s : 0 < s := by omega
      have hPosB : B.edge 0 (f s) (f a) := by
        have h := (E.toMeetEmbedding.edge_iff
          0 s a h0s hsa han).mpr hPosA
        simpa only [E.toMeetEmbedding.marker_zero] using h
      exact ⟨a,ha,hsa,han,hPosA,hPosB⟩
    · intro s hs
      obtain ⟨a,b,hab,hbn,ha,hb,hsa,hPosA⟩ :=
        finite_twoSplit_exists_positive_anchor DA s hs
      have hPosB : B.edge (f s) (f a) (f b) :=
        (E.toMeetEmbedding.edge_iff s a b hsa hab hbn).mpr hPosA
      exact ⟨a,b,hab,hbn,ha,hb,hsa,hPosA,hPosB⟩
  · rintro ⟨hOne,hTwo⟩
    exact finite_leafPreembedding_to_boundedEmbedding_of_positive_anchors
      DA DB Q hOne hTwo

end DiaryLeafPriority
end ThreeUniformDiaries
