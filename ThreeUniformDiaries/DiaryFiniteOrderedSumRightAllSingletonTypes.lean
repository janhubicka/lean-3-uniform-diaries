import ThreeUniformDiaries.DiaryFiniteOrderedSumRightMarkerTypes
import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface
import ThreeUniformDiaries.DiaryFiniteOrderedSumPermittedEdges

/-!
# All translated-right singleton types at original nonmarker cuts

The old transport theorem covered two right LEAVES. For protection
of a finite diary embedding one also needs comparison of two split
vertices, and of a split with a leaf. Here the source is a finite
V/E pre-diary block, NOT a RolePrediary on the artificial Nat tail.

The cases are exhaustive:
* two leaves: the verified right-leaf uniform-column theorem;
* two splits: E1--E5 forbid all later incoming tests, reducing
  both source and target singleton types to the three markers;
* split versus leaf: their first three marker profiles disagree
  in both source and target, making both prefix-equality claims
  false at every cut >=3.

The result is exact two-way type transport for ANY right nonmarker
source vertices, at ALL translated original cuts >=3, without
postulating S1/S2 or assuming the output is a pre-diary.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- Both one-split and two-split roles of a genuine right
source vertex are transported and reflected literally. -/
theorem finiteTwoBlockCarrier_right_isDiarySplit_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (z : Nat) (hz3 : 3 ≤ z) (hzm : z < m) :
    IsDiarySplit (finiteTwoBlockCarrier H K n m bits)
        (rightBlockImage n z) ↔ IsDiarySplit K z := by
  unfold IsDiarySplit
  exact or_congr
    (finiteTwoBlockCarrier_right_oneSplit_iff
      FH FK bits z hz3 hzm)
    (finiteTwoBlockCarrier_right_twoSplit_iff
      FH FK bits z hz3 hzm)

/-- Exact singleton type preservation AND reflection at
every translated right cut l>=3, for arbitrary right NONMARKER
vertices including mixed roles and equal vertices. -/
theorem finiteTwoBlockCarrier_right_oneType_general_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (PK : FiniteRolePrediaryBlock K m)
    (hEH : ∀ x y z : Nat, H.edge x y z →
      PermittedDiaryEdge H x y z)
    (bits : Nat → Bool)
    (l u v : Nat) (hl3 : 3 ≤ l)
    (hu3 : 3 ≤ u) (hum : u < m)
    (hv3 : 3 ≤ v) (hvm : v < m) :
    ((finiteTwoBlockCarrier H K n m bits).SameOneTypeBelow
        (rightBlockImage n l)
        (rightBlockImage n u) (rightBlockImage n v) ↔
      K.SameOneTypeBelow l u v) := by
  let G := finiteTwoBlockCarrier H K n m bits
  have hE : ∀ x y z : Nat, G.edge x y z →
      PermittedDiaryEdge G x y z := by
    intro x y z he
    exact finiteTwoBlockCarrier_permitted_edge
      FH PK.frame hEH PK.permitted_edge bits x y z he
  have hTarget3 : 3 ≤ rightBlockImage n l := by
    have hge := rightBlockImage_nonmarker_ge
      n l FH.length_ge_three hl3
    have hn3 := FH.length_ge_three
    omega
  by_cases huLeaf : IsLeaf K u
  · by_cases hvLeaf : IsLeaf K v
    · exact finiteTwoBlockCarrier_right_leaf_oneType_iff
        FH PK.frame PK.permitted_edge bits l u v hl3
        hu3 hum huLeaf hv3 hvm hvLeaf
    · have hvSplit : IsDiarySplit K v := by
        rcases PK.role_valid v hv3 hvm with hvL | hvOne | hvTwo
        · exact False.elim (hvLeaf hvL)
        · exact Or.inl hvOne
        · exact Or.inr hvTwo
      have hSourceNot3 :=
        leaf_split_not_sameOneType_three K u v huLeaf hvSplit
      have hTargetLeaf : IsLeaf G (rightBlockImage n u) :=
        (finiteTwoBlockCarrier_right_leaf_iff
          FH PK.frame bits u hu3 hum).mpr huLeaf
      have hTargetSplit : IsDiarySplit G (rightBlockImage n v) :=
        (finiteTwoBlockCarrier_right_isDiarySplit_iff
          FH PK.frame bits v hv3 hvm).mpr hvSplit
      have hTargetNot3 :=
        leaf_split_not_sameOneType_three G
          (rightBlockImage n u) (rightBlockImage n v)
          hTargetLeaf hTargetSplit
      have hSourceNot : ¬ K.SameOneTypeBelow l u v := by
        intro h
        exact hSourceNot3 (by
          intro a b hab hb
          exact h hab (by omega))
      have hTargetNot :
          ¬ G.SameOneTypeBelow (rightBlockImage n l)
              (rightBlockImage n u) (rightBlockImage n v) := by
        intro h
        exact hTargetNot3 (by
          intro a b hab hb
          exact h hab (by omega))
      exact iff_of_false hTargetNot hSourceNot
  · have huSplit : IsDiarySplit K u := by
      rcases PK.role_valid u hu3 hum with huL | huOne | huTwo
      · exact False.elim (huLeaf huL)
      · exact Or.inl huOne
      · exact Or.inr huTwo
    by_cases hvLeaf : IsLeaf K v
    · have hSourceNot3 :=
        split_leaf_not_sameOneType_three K u v huSplit hvLeaf
      have hTargetSplit : IsDiarySplit G (rightBlockImage n u) :=
        (finiteTwoBlockCarrier_right_isDiarySplit_iff
          FH PK.frame bits u hu3 hum).mpr huSplit
      have hTargetLeaf : IsLeaf G (rightBlockImage n v) :=
        (finiteTwoBlockCarrier_right_leaf_iff
          FH PK.frame bits v hv3 hvm).mpr hvLeaf
      have hTargetNot3 :=
        split_leaf_not_sameOneType_three G
          (rightBlockImage n u) (rightBlockImage n v)
          hTargetSplit hTargetLeaf
      have hSourceNot : ¬ K.SameOneTypeBelow l u v := by
        intro h
        exact hSourceNot3 (by
          intro a b hab hb
          exact h hab (by omega))
      have hTargetNot :
          ¬ G.SameOneTypeBelow (rightBlockImage n l)
              (rightBlockImage n u) (rightBlockImage n v) := by
        intro h
        exact hTargetNot3 (by
          intro a b hab hb
          exact h hab (by omega))
      exact iff_of_false hTargetNot hSourceNot
    · have hvSplit : IsDiarySplit K v := by
        rcases PK.role_valid v hv3 hvm with hvL | hvOne | hvTwo
        · exact False.elim (hvLeaf hvL)
        · exact Or.inl hvOne
        · exact Or.inr hvTwo
      have huTarget : IsDiarySplit G (rightBlockImage n u) :=
        (finiteTwoBlockCarrier_right_isDiarySplit_iff
          FH PK.frame bits u hu3 hum).mpr huSplit
      have hvTarget : IsDiarySplit G (rightBlockImage n v) :=
        (finiteTwoBlockCarrier_right_isDiarySplit_iff
          FH PK.frame bits v hv3 hvm).mpr hvSplit
      calc
        G.SameOneTypeBelow (rightBlockImage n l)
            (rightBlockImage n u) (rightBlockImage n v) ↔
          G.SameOneTypeBelow 3
            (rightBlockImage n u) (rightBlockImage n v) :=
            E_split_oneType_stable hE
              (rightBlockImage n l)
              (rightBlockImage n u) (rightBlockImage n v)
              hTarget3 huTarget hvTarget
        _ ↔ K.SameOneTypeBelow 3 u v :=
          finiteTwoBlockCarrier_right_oneType_marker_iff
            FH PK.frame bits 3 u v (by omega)
        _ ↔ K.SameOneTypeBelow l u v :=
          (E_split_oneType_stable PK.permitted_edge
            l u v hl3 huSplit hvSplit).symm

end DiaryLeafPriority
end ThreeUniformDiaries
