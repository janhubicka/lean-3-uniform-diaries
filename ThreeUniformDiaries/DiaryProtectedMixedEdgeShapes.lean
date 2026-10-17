import ThreeUniformDiaries.DiaryOnePassTargetPrediary
import ThreeUniformDiaries.DiaryPrediaryRoleNextCut

/-!
# E-only exclusions for protected mixed singleton and pair meets

The source and target diary may contain protected copies with
arbitrary ordered pairs, including pairs having one-split or
two-split members. The global one-pass full pair-type transport
proved for pairs of LEAVES does not automatically cover these
mixed pairs. We therefore isolate the role consequences that
make the mixed case simpler.

For a pair containing a genuine split, a positive auxiliary
coordinate x>0 is impossible: E3--E5 require BOTH pair members
to be leaves, while E1/E2 require x=0. For singleton types of
split vertices, any test with middle coordinate b>=3 is also
impossible, since only the role-marker E1 edges may end at a
split vertex. These are literal facts about the ternary edge
relation, with no S1/S2 or completion assumptions.

These lemmas are the first stage of protected mixed-meet
transport, NOT a proof of the full protected embedding clause
or the every-flip absorption direction.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- A first-class helper for the source/target marker-defined
split roles, without introducing a new redundant structure. -/
def IsDiarySplit (H : Ordered3Graph Nat) (z : Nat) : Prop :=
  IsOneSplit H z ∨ IsTwoSplit H z

/-- A genuine split vertex cannot simultaneously be a leaf. -/
theorem IsDiarySplit.not_leaf
    {H : Ordered3Graph Nat} {z : Nat}
    (hz : IsDiarySplit H z) :
    ¬ IsLeaf H z := by
  intro hl
  rcases hz with hOne | hTwo
  · exact hl.2.1 hOne.2.1
  · exact hl.2.2 hTwo.2.2

/-- A mixed ordered pair contains at least one non-leaf split,
which excludes the all-leaf E3/E4/E5 edge forms. -/
theorem RolePrediary.mixed_pair_no_positive_aux_edge
    (P : RolePrediary H) (x a b : Nat)
    (hx : 0 < x)
    (hMixed : IsDiarySplit H a ∨ IsDiarySplit H b) :
    ¬ H.edge x a b := by
  have hNotBothLeaf : ¬ (IsLeaf H a ∧ IsLeaf H b) := by
    rintro ⟨ha, hb⟩
    rcases hMixed with hA | hB
    · exact (IsDiarySplit.not_leaf hA) ha
    · exact (IsDiarySplit.not_leaf hB) hb
  intro he
  rcases P.permitted_edge x a b he with
      hMarker | hOne | hTwo | hDevlin | hNormal
  · have hZero : x = 0 := hMarker.1
    omega
  · have hZero : x = 0 := hOne.1
    omega
  · exact hNotBothLeaf ⟨hTwo.2.1, hTwo.2.2⟩
  · exact hNotBothLeaf ⟨hDevlin.2.1, hDevlin.2.2⟩
  · exact hNotBothLeaf ⟨hNormal.2.1, hNormal.2.2⟩

/-- A split endpoint has no incoming non-marker hyperedge whose
middle coordinate is at least three. This is the E-only source
of identical later singleton columns for equal-role splits. -/
theorem RolePrediary.split_no_late_singleton_test
    (P : RolePrediary H) (a b z : Nat)
    (hz : IsDiarySplit H z)
    (hb : 3 ≤ b) :
    ¬ H.edge a b z := by
  have hNotLeaf : ¬ IsLeaf H z := hz.not_leaf
  intro he
  rcases P.permitted_edge a b z he with
      hMarker | hOne | hTwo | hDevlin | hNormal
  · rcases hMarker.2.1 with h | h <;> omega
  · exact hNotLeaf hOne.2.2
  · exact hNotLeaf hTwo.2.2
  · exact hNotLeaf hDevlin.2.2
  · exact hNotLeaf hNormal.2.2

/-- Two genuinely mixed pair patterns have identical auxiliary
tests at every positive coordinate, regardless of their roles'
relative positions. Only the marker coordinate zero may differ. -/
theorem RolePrediary.mixed_pairs_positive_aux_agree
    (P : RolePrediary H) (a b c d m : Nat)
    (hAB : IsDiarySplit H a ∨ IsDiarySplit H b)
    (hCD : IsDiarySplit H c ∨ IsDiarySplit H d) :
    ∀ x : Nat, 0 < x → x < m →
      (H.edge x a b ↔ H.edge x c d) := by
  intro x hx _hm
  exact iff_of_false
    (P.mixed_pair_no_positive_aux_edge x a b hx hAB)
    (P.mixed_pair_no_positive_aux_edge x c d hx hCD)

end DiaryLeafPriority
end ThreeUniformDiaries
