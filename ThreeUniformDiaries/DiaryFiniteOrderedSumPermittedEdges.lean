import ThreeUniformDiaries.DiaryFiniteOrderedSumRoles
import ThreeUniformDiaries.DiaryFiniteOrderedSumBoundedEmbedding

/-!
# The complete permitted E1--E5 shapes in finite ordered sums

The actual raw two-block carrier has three sorts of edges:
(1) internal left edges, (2) translated internal right edges, and
(3) cross Devlin marker edges of the explicit forms (1,u,v),
(2,u,v), with u a left leaf and v a right leaf.

Assume both bounded source edge tables have E1--E5 permitted shapes.
The verified induced-copy and marker-role transport theorems
show that every target edge also has an E1--E5 permitted shape
relative to the ACTUAL target marker-derived roles. This is
independent of how cross orientation bits were selected.

The result proves the E restriction and ordered finite support;
it does NOT assert the V1/V2 witness/coherence or global V3
axioms required for an ambient pre-diary.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- Every copied left edge retains its genuine permitted shape
in the raw carrier because all its participating marker-defined
roles are preserved and reflected. -/
theorem finiteTwoBlockCarrier_left_permitted
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hE : ∀ x y z : Nat, H.edge x y z →
      PermittedDiaryEdge H x y z)
    (bits : Nat → Bool)
    (x y z : Nat) (he : H.edge x y z) :
    PermittedDiaryEdge (finiteTwoBlockCarrier H K n m bits) x y z := by
  have hSupp := FH.edge_support x y z he
  have hxN : x < n := by omega
  have hyN : y < n := by omega
  have hzN : z < n := hSupp.2.2.2
  rcases hE x y z he with hRole | hOne | hTwo | hDevlin | hNormal
  · exact Or.inl hRole
  · exact Or.inr (Or.inl
      ⟨hOne.1,
       (finiteTwoBlockCarrier_left_oneSplit_iff
         FH FK bits y hyN).mpr hOne.2.1,
       (finiteTwoBlockCarrier_left_leaf_iff
         FH FK bits z hzN).mpr hOne.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨(finiteTwoBlockCarrier_left_twoSplit_iff
          FH FK bits x hxN).mpr hTwo.1,
       (finiteTwoBlockCarrier_left_leaf_iff
          FH FK bits y hyN).mpr hTwo.2.1,
       (finiteTwoBlockCarrier_left_leaf_iff
          FH FK bits z hzN).mpr hTwo.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hDevlin.1,
       (finiteTwoBlockCarrier_left_leaf_iff
         FH FK bits y hyN).mpr hDevlin.2.1,
       (finiteTwoBlockCarrier_left_leaf_iff
         FH FK bits z hzN).mpr hDevlin.2.2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨(finiteTwoBlockCarrier_left_leaf_iff
         FH FK bits x hxN).mpr hNormal.1,
       (finiteTwoBlockCarrier_left_leaf_iff
         FH FK bits y hyN).mpr hNormal.2.1,
       (finiteTwoBlockCarrier_left_leaf_iff
         FH FK bits z hzN).mpr hNormal.2.2⟩)))

/-- The complete permitted-edge shape of an internal right edge
survives its translation, including the three initial markers. -/
theorem finiteTwoBlockCarrier_right_permitted
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hE : ∀ a b c : Nat, K.edge a b c →
      PermittedDiaryEdge K a b c)
    (bits : Nat → Bool)
    (a b c : Nat) (he : K.edge a b c) :
    PermittedDiaryEdge (finiteTwoBlockCarrier H K n m bits)
      (rightBlockImage n a) (rightBlockImage n b)
      (rightBlockImage n c) := by
  let G := finiteTwoBlockCarrier H K n m bits
  let f := rightBlockImage n
  have hSupp := FK.edge_support a b c he
  have haM : a < m := by omega
  have hbM : b < m := by omega
  have hcM : c < m := hSupp.2.2.2
  rcases hE a b c he with hRole | hOne | hTwo | hDevlin | hNormal
  · obtain ⟨ha0, hbMark, hc3⟩ := hRole
    subst a
    have hcTarget : 3 ≤ f c := by
      change 3 ≤ rightBlockImage n c
      have hge := rightBlockImage_nonmarker_ge n c
        FH.length_ge_three hc3
      have hn3 := FH.length_ge_three
      omega
    rcases hbMark with hb1 | hb2
    · subst b
      exact Or.inl
        ⟨by simp [f, rightBlockImage],
         Or.inl (by simp [f, rightBlockImage]), hcTarget⟩
    · subst b
      exact Or.inl
        ⟨by simp [f, rightBlockImage],
         Or.inr (by simp [f, rightBlockImage]), hcTarget⟩
  · obtain ⟨ha0, hbRole, hcRole⟩ := hOne
    subst a
    have hbG : IsOneSplit G (f b) :=
      (finiteTwoBlockCarrier_right_oneSplit_iff
        FH FK bits b hbRole.1 hbM).mpr hbRole
    have hcG : IsLeaf G (f c) :=
      (finiteTwoBlockCarrier_right_leaf_iff
        FH FK bits c hcRole.1 hcM).mpr hcRole
    exact Or.inr (Or.inl
      ⟨by simp [f, rightBlockImage], hbG, hcG⟩)
  · obtain ⟨haRole, hbRole, hcRole⟩ := hTwo
    have haG : IsTwoSplit G (f a) :=
      (finiteTwoBlockCarrier_right_twoSplit_iff
        FH FK bits a haRole.1 haM).mpr haRole
    have hbG : IsLeaf G (f b) :=
      (finiteTwoBlockCarrier_right_leaf_iff
        FH FK bits b hbRole.1 hbM).mpr hbRole
    have hcG : IsLeaf G (f c) :=
      (finiteTwoBlockCarrier_right_leaf_iff
        FH FK bits c hcRole.1 hcM).mpr hcRole
    exact Or.inr (Or.inr (Or.inl ⟨haG,hbG,hcG⟩))
  · obtain ⟨haMark, hbRole, hcRole⟩ := hDevlin
    have hbG : IsLeaf G (f b) :=
      (finiteTwoBlockCarrier_right_leaf_iff
        FH FK bits b hbRole.1 hbM).mpr hbRole
    have hcG : IsLeaf G (f c) :=
      (finiteTwoBlockCarrier_right_leaf_iff
        FH FK bits c hcRole.1 hcM).mpr hcRole
    have haMarker : f a = 1 ∨ f a = 2 := by
      rcases haMark with ha1 | ha2
      · subst a
        exact Or.inl (by simp [f, rightBlockImage])
      · subst a
        exact Or.inr (by simp [f, rightBlockImage])
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨haMarker,hbG,hcG⟩)))
  · obtain ⟨haRole, hbRole, hcRole⟩ := hNormal
    have haG : IsLeaf G (f a) :=
      (finiteTwoBlockCarrier_right_leaf_iff
        FH FK bits a haRole.1 haM).mpr haRole
    have hbG : IsLeaf G (f b) :=
      (finiteTwoBlockCarrier_right_leaf_iff
        FH FK bits b hbRole.1 hbM).mpr hbRole
    have hcG : IsLeaf G (f c) :=
      (finiteTwoBlockCarrier_right_leaf_iff
        FH FK bits c hcRole.1 hcM).mpr hcRole
    exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨haG,hbG,hcG⟩)))

/-- Every edge of the actual raw two-block carrier satisfies
one of the five permitted diary E forms relative to the
TARGET roles, assuming only source finite frames and the
source permitted E edge-shape restrictions. -/
theorem finiteTwoBlockCarrier_permitted_edge
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hEH : ∀ x y z : Nat, H.edge x y z →
      PermittedDiaryEdge H x y z)
    (hEK : ∀ a b c : Nat, K.edge a b c →
      PermittedDiaryEdge K a b c)
    (bits : Nat → Bool)
    (x y z : Nat)
    (he : (finiteTwoBlockCarrier H K n m bits).edge x y z) :
    PermittedDiaryEdge (finiteTwoBlockCarrier H K n m bits)
      x y z := by
  let G := finiteTwoBlockCarrier H K n m bits
  rcases he with hLeft | hRight | hCross
  · exact finiteTwoBlockCarrier_left_permitted
      FH FK hEH bits x y z hLeft.1
  · obtain ⟨a,b,c,hK,hcm,hx,hy,hz⟩ := hRight
    subst x
    subst y
    subst z
    exact finiteTwoBlockCarrier_right_permitted
      FH FK hEK bits a b c hK
  · obtain ⟨u,v,hu3,hun,huRole,hv3,hvm,hvRole,hy,hz,hBit⟩ := hCross
    have huG : IsLeaf G u :=
      (finiteTwoBlockCarrier_left_leaf_iff FH FK bits u hun).mpr huRole
    have hvG : IsLeaf G (rightBlockImage n v) :=
      (finiteTwoBlockCarrier_right_leaf_iff
        FH FK bits v hv3 hvm).mpr hvRole
    have hxMarker : x = 1 ∨ x = 2 :=
      hBit.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    subst y
    subst z
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hxMarker,huG,hvG⟩)))

end DiaryLeafPriority
end ThreeUniformDiaries
