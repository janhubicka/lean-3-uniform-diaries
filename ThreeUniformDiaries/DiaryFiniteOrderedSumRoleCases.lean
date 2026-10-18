import ThreeUniformDiaries.DiaryFiniteOrderedSumBoundedEmbedding
import ThreeUniformDiaries.DiaryFiniteOrderedSumRoles

/-!
# Exhaustive finite ordered-sum vertex and role classification

The two-block carrier identifies only the marker vertices 0,1,2.
Every nonmarker z in the final bounded frame either is an original
left vertex z<n or has a UNIQUE actual right original address
v = z-(n-3), with z = rightBlockImage n v and 3<=v<m.

These facts prevent accidental assumptions about vertices beyond
the finite frame and allow us to lift all *local* V1/V2/V3/witness
statements to unrestricted quantifiers over target finite roles.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- Complete arithmetic classification of a nonmarker vertex
inside the bounded carrier, with no mathematical edge assumptions. -/
theorem finiteTwoBlock_nonmarker_cases
    (hn : 3 ≤ n) (hm : 3 ≤ m)
    (z : Nat) (hz3 : 3 ≤ z)
    (hBound : z < finiteTwoBlockLength n m) :
    z < n ∨
      ∃ v : Nat, 3 ≤ v ∧ v < m ∧ z = rightBlockImage n v := by
  by_cases hzn : z < n
  · exact Or.inl hzn
  · have hzn' : n ≤ z := by omega
    let v := z - (n - 3)
    have hv3 : 3 ≤ v := by
      dsimp [v]
      omega
    have hvm : v < m := by
      dsimp [v, finiteTwoBlockLength] at *
      omega
    have hImage : z = rightBlockImage n v := by
      have hvNot : ¬ v < 3 := by omega
      simp only [rightBlockImage, if_neg hvNot]
      dsimp [v]
      omega
    exact Or.inr ⟨v,hv3,hvm,hImage⟩

/-- Every actual finite target leaf comes from precisely one of
the two indicated source blocks, with exact marker role recovery. -/
theorem finiteTwoBlock_leaf_cases
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool) (z : Nat)
    (hz : IsLeaf (finiteTwoBlockCarrier H K n m bits) z)
    (hBound : z < finiteTwoBlockLength n m) :
    (z < n ∧ IsLeaf H z) ∨
      ∃ v : Nat, 3 ≤ v ∧ v < m ∧
        IsLeaf K v ∧ z = rightBlockImage n v := by
  rcases finiteTwoBlock_nonmarker_cases
    FH.length_ge_three FK.length_ge_three z hz.1 hBound with
      hLeft | ⟨v,hv3,hvm,hEq⟩
  · exact Or.inl ⟨hLeft,
      (finiteTwoBlockCarrier_left_leaf_iff
        FH FK bits z hLeft).mp hz⟩
  · subst z
    exact Or.inr ⟨v,hv3,hvm,
      (finiteTwoBlockCarrier_right_leaf_iff
        FH FK bits v hv3 hvm).mp hz,rfl⟩

/-- Every actual 1-split in the bounded target originates
in one of the finite input blocks. -/
theorem finiteTwoBlock_oneSplit_cases
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool) (z : Nat)
    (hz : IsOneSplit (finiteTwoBlockCarrier H K n m bits) z)
    (hBound : z < finiteTwoBlockLength n m) :
    (z < n ∧ IsOneSplit H z) ∨
      ∃ v : Nat, 3 ≤ v ∧ v < m ∧
        IsOneSplit K v ∧ z = rightBlockImage n v := by
  rcases finiteTwoBlock_nonmarker_cases
    FH.length_ge_three FK.length_ge_three z hz.1 hBound with
      hLeft | ⟨v,hv3,hvm,hEq⟩
  · exact Or.inl ⟨hLeft,
      (finiteTwoBlockCarrier_left_oneSplit_iff
        FH FK bits z hLeft).mp hz⟩
  · subst z
    exact Or.inr ⟨v,hv3,hvm,
      (finiteTwoBlockCarrier_right_oneSplit_iff
        FH FK bits v hv3 hvm).mp hz,rfl⟩

/-- Every actual 2-split in the bounded target originates
in one of the finite input blocks. -/
theorem finiteTwoBlock_twoSplit_cases
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool) (z : Nat)
    (hz : IsTwoSplit (finiteTwoBlockCarrier H K n m bits) z)
    (hBound : z < finiteTwoBlockLength n m) :
    (z < n ∧ IsTwoSplit H z) ∨
      ∃ v : Nat, 3 ≤ v ∧ v < m ∧
        IsTwoSplit K v ∧ z = rightBlockImage n v := by
  rcases finiteTwoBlock_nonmarker_cases
    FH.length_ge_three FK.length_ge_three z hz.1 hBound with
      hLeft | ⟨v,hv3,hvm,hEq⟩
  · exact Or.inl ⟨hLeft,
      (finiteTwoBlockCarrier_left_twoSplit_iff
        FH FK bits z hLeft).mp hz⟩
  · subst z
    exact Or.inr ⟨v,hv3,hvm,
      (finiteTwoBlockCarrier_right_twoSplit_iff
        FH FK bits v hv3 hvm).mp hz,rfl⟩

end DiaryLeafPriority
end ThreeUniformDiaries
