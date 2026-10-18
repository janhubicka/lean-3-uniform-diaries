import ThreeUniformDiaries.DiaryFiniteOrderedSumFuturePrefix
import ThreeUniformDiaries.DiaryFiniteOrderedSumBoundedEmbedding
import ThreeUniformDiaries.DiaryFiniteOrderedSumRoles

/-!
# Right-block singleton type transport in finite ordered sums

The translated right block is induced, but its leaf singleton
columns gain new tests at left-block vertices. These tests are
uniform across all right leaves: the only possible nonzero ones
are the cross Devlin marker incidences.

We prove the exact two-way transport of singleton type agreement
through each translated original right cut. The proof separates
three cases for the middle coordinate of an edge test:
* in the left block: uniform future-leaf tests;
* in the right block with an earlier marker/right coordinate:
  the induced right embedding;
* in the right block with a first vertex from the left nonmarker
  block: no edge is permitted by the actual carrier definition.

This is a reusable ingredient for V1 coherence on right splits.
No source/target global pre-diary or S1/S2 axiom is assumed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- An edge cannot start at a left nonmarker vertex and end in
the right block. Cross edges only start at Devlin markers 1,2;
right-copy edges start at a marker or a translated right vertex. -/
theorem finiteTwoBlockCarrier_no_left_nonmarker_first_to_right
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (a b c : Nat) (ha3 : 3 ≤ a) (han : a < n) (hcn : n ≤ c) :
    ¬ (finiteTwoBlockCarrier H K n m bits).edge a b c := by
  intro he
  rcases he with hLeft | hRight | hCross
  · omega
  · obtain ⟨a', b', c', hK, _hc, ha, _hb, _hz⟩ := hRight
    by_cases haSmall : a' < 3
    · rw [rightBlockImage_marker n a' haSmall] at ha
      omega
    · have haRight : n ≤ rightBlockImage n a' :=
        rightBlockImage_nonmarker_ge n a'
          FH.length_ge_three (by omega)
      omega
  · obtain ⟨u, v, _hu3, _hun, _hlu, _hv3, _hvm, _hlv,
        _hy, _hz, hBit⟩ := hCross
    rcases hBit with hOne | hTwo
    · omega
    · omega

/-- The entire translated-right singleton type prefix agrees
iff the corresponding original right type prefix agrees, for
genuine right leaves and cuts at or beyond the three markers.
The cross orientation bits are completely arbitrary. -/
theorem finiteTwoBlockCarrier_right_leaf_oneType_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hshape : ∀ a b c : Nat, K.edge a b c →
      PermittedDiaryEdge K a b c)
    (bits : Nat → Bool)
    (l v w : Nat) (hl3 : 3 ≤ l)
    (hv3 : 3 ≤ v) (hvm : v < m) (hvLeaf : IsLeaf K v)
    (hw3 : 3 ≤ w) (hwm : w < m) (hwLeaf : IsLeaf K w) :
    ((finiteTwoBlockCarrier H K n m bits).SameOneTypeBelow
        (rightBlockImage n l)
        (rightBlockImage n v) (rightBlockImage n w) ↔
      K.SameOneTypeBelow l v w) := by
  let G := finiteTwoBlockCarrier H K n m bits
  have hn3 : 3 ≤ n := FH.length_ge_three
  have hMon := rightBlockImage_strictMono n hn3
  constructor
  · intro hTarget a b hab hb
    have hAB : rightBlockImage n a < rightBlockImage n b :=
      hMon hab
    have hBL : rightBlockImage n b < rightBlockImage n l :=
      hMon hb
    have ht := hTarget
      (rightBlockImage n a) (rightBlockImage n b) hAB hBL
    have hv := finiteTwoBlockCarrier_right_edge_iff_all
      FH FK bits a b v
    have hw := finiteTwoBlockCarrier_right_edge_iff_all
      FH FK bits a b w
    exact hv.symm.trans (ht.trans hw)
  · intro hSource a b hab hb
    by_cases hbn : b < n
    · have hv := finiteTwoBlockCarrier_right_leaf_column_iff
        FH FK hshape bits a b v hab hbn hv3 hvm hvLeaf
      have hw := finiteTwoBlockCarrier_right_leaf_column_iff
        FH FK hshape bits a b w hab hbn hw3 hwm hwLeaf
      exact hv.trans hw.symm
    · have hbge : n ≤ b := by omega
      have hbl : b < l + (n - 3) := by
        have hnot : ¬ l < 3 := by omega
        have himage : rightBlockImage n l = l + (n - 3) := by
          simp only [rightBlockImage, if_neg hnot]
        simpa only [himage] using hb
      have hb0ge : 3 ≤ b - (n - 3) := by omega
      have hb0lt : b - (n - 3) < l := by omega
      have hbimage :
          rightBlockImage n (b - (n - 3)) = b := by
        have hnot : ¬ b - (n - 3) < 3 := by omega
        simp only [rightBlockImage, if_neg hnot]
        omega
      by_cases haGap : 3 ≤ a ∧ a < n
      · have hvg : n ≤ rightBlockImage n v :=
          rightBlockImage_nonmarker_ge n v hn3 hv3
        have hwg : n ≤ rightBlockImage n w :=
          rightBlockImage_nonmarker_ge n w hn3 hw3
        exact iff_of_false
          (finiteTwoBlockCarrier_no_left_nonmarker_first_to_right
            FH FK bits a b (rightBlockImage n v)
            haGap.1 haGap.2 hvg)
          (finiteTwoBlockCarrier_no_left_nonmarker_first_to_right
            FH FK bits a b (rightBlockImage n w)
            haGap.1 haGap.2 hwg)
      · by_cases haSmall : a < 3
        · have hZero : rightBlockImage n a = a :=
            rightBlockImage_marker n a haSmall
          have hab0 : a < b - (n - 3) := by omega
          have hs := hSource a (b - (n - 3)) hab0 hb0lt
          have hv := finiteTwoBlockCarrier_right_edge_iff_all
            FH FK bits a (b - (n - 3)) v
          have hw := finiteTwoBlockCarrier_right_edge_iff_all
            FH FK bits a (b - (n - 3)) w
          rw [hZero, hbimage] at hv hw
          exact hv.trans (hs.trans hw.symm)
        · have hage : n ≤ a := by
            by_contra hnot
            have hlt : a < n := by omega
            exact haGap ⟨by omega, hlt⟩
          have ha0ge : 3 ≤ a - (n - 3) := by omega
          have haimage :
              rightBlockImage n (a - (n - 3)) = a := by
            have hnot : ¬ a - (n - 3) < 3 := by omega
            simp only [rightBlockImage, if_neg hnot]
            omega
          have hab0 :
              a - (n - 3) < b - (n - 3) := by omega
          have hs := hSource
            (a - (n - 3)) (b - (n - 3)) hab0 hb0lt
          have hv := finiteTwoBlockCarrier_right_edge_iff_all
            FH FK bits (a - (n - 3)) (b - (n - 3)) v
          have hw := finiteTwoBlockCarrier_right_edge_iff_all
            FH FK bits (a - (n - 3)) (b - (n - 3)) w
          rw [haimage, hbimage] at hv hw
          exact hv.trans (hs.trans hw.symm)

end DiaryLeafPriority
end ThreeUniformDiaries
