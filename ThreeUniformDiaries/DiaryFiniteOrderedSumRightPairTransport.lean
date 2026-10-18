import ThreeUniformDiaries.DiaryFiniteOrderedSumRightSingletonTransport

/-!
# Full right-block pair-type transport in finite ordered sums

The right-side singleton-prefix theorem handles both coordinate
types of ordered leaf pairs. Auxiliary pair tests are simpler:
the translated right copy reflects their genuine tests, while
new levels of the left nonmarker block cannot be first
coordinates of an edge ending in the right block. Marker tests
are still copied and reflected by the global induced embedding.

Thus the entire right-pair auxiliary type, and then its full
two-type, are preserved AND reflected at the translated cut.
No global target V/E/S axioms are assumed. This is the second
input to the right-block V2-coherence verification.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- Exact auxiliary pair-type transport. Only the final
members b,d of the two source pairs need lie beyond markers,
so a test in the left nonmarker gap is always a nonedge.
No E/V/S coherence hypothesis is needed. -/
theorem finiteTwoBlockCarrier_right_pair_auxType_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (l a b c d : Nat) (hl3 : 3 ≤ l)
    (hb3 : 3 ≤ b) (hd3 : 3 ≤ d) :
    ((finiteTwoBlockCarrier H K n m bits).SameAuxTypeBelow
        (rightBlockImage n l)
        (rightBlockImage n a) (rightBlockImage n b)
        (rightBlockImage n c) (rightBlockImage n d) ↔
      K.SameAuxTypeBelow l a b c d) := by
  have hn3 := FH.length_ge_three
  have hMon := rightBlockImage_strictMono n hn3
  constructor
  · intro hTarget x hx
    have hXL : rightBlockImage n x < rightBlockImage n l :=
      hMon hx
    have ht := hTarget (a := rightBlockImage n x) hXL
    have hab := finiteTwoBlockCarrier_right_edge_iff_all
      FH FK bits x a b
    have hcd := finiteTwoBlockCarrier_right_edge_iff_all
      FH FK bits x c d
    exact hab.symm.trans (ht.trans hcd)
  · intro hSource x hx
    by_cases hxn : x < n
    · by_cases hxSmall : x < 3
      · have hImage : rightBlockImage n x = x :=
          rightBlockImage_marker n x hxSmall
        have hXL : x < l := by omega
        have hs := hSource (a := x) hXL
        have hab := finiteTwoBlockCarrier_right_edge_iff_all
          FH FK bits x a b
        have hcd := finiteTwoBlockCarrier_right_edge_iff_all
          FH FK bits x c d
        rw [hImage] at hab hcd
        exact hab.trans (hs.trans hcd.symm)
      · have hx3 : 3 ≤ x := by omega
        have hbN : n ≤ rightBlockImage n b :=
          rightBlockImage_nonmarker_ge n b hn3 hb3
        have hdN : n ≤ rightBlockImage n d :=
          rightBlockImage_nonmarker_ge n d hn3 hd3
        exact iff_of_false
          (finiteTwoBlockCarrier_no_left_nonmarker_first_to_right
            FH FK bits x (rightBlockImage n a)
            (rightBlockImage n b) hx3 hxn hbN)
          (finiteTwoBlockCarrier_no_left_nonmarker_first_to_right
            FH FK bits x (rightBlockImage n c)
            (rightBlockImage n d) hx3 hxn hdN)
    · have hxN : n ≤ x := by omega
      have hnotL : ¬ l < 3 := by omega
      have hLImage : rightBlockImage n l = l + (n - 3) := by
        simp only [rightBlockImage, if_neg hnotL]
      have hx0lt : x - (n - 3) < l := by
        rw [hLImage] at hx
        omega
      have hx0ge : 3 ≤ x - (n - 3) := by omega
      have hXImage : rightBlockImage n (x - (n - 3)) = x := by
        have hnot : ¬ x - (n - 3) < 3 := by omega
        simp only [rightBlockImage, if_neg hnot]
        omega
      have hs := hSource (a := x - (n - 3)) hx0lt
      have hab := finiteTwoBlockCarrier_right_edge_iff_all
        FH FK bits (x - (n - 3)) a b
      have hcd := finiteTwoBlockCarrier_right_edge_iff_all
        FH FK bits (x - (n - 3)) c d
      rw [hXImage] at hab hcd
      exact hab.trans (hs.trans hcd.symm)

/-- Full ordered-pair type transport on genuine right leaf pairs.
Both singleton coordinates and all auxiliary tests are carried
through exactly, for arbitrary cross orientation choices. -/
theorem finiteTwoBlockCarrier_right_leaf_twoType_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hshape : ∀ a b c : Nat, K.edge a b c →
      PermittedDiaryEdge K a b c)
    (bits : Nat → Bool)
    (l a b c d : Nat) (hl3 : 3 ≤ l)
    (ha3 : 3 ≤ a) (ham : a < m) (haLeaf : IsLeaf K a)
    (hb3 : 3 ≤ b) (hbm : b < m) (hbLeaf : IsLeaf K b)
    (hc3 : 3 ≤ c) (hcm : c < m) (hcLeaf : IsLeaf K c)
    (hd3 : 3 ≤ d) (hdm : d < m) (hdLeaf : IsLeaf K d) :
    ((finiteTwoBlockCarrier H K n m bits).SameTwoTypeBelow
        (rightBlockImage n l)
        (rightBlockImage n a) (rightBlockImage n b)
        (rightBlockImage n c) (rightBlockImage n d) ↔
      K.SameTwoTypeBelow l a b c d) := by
  have hFirst := finiteTwoBlockCarrier_right_leaf_oneType_iff
    FH FK hshape bits l a c hl3
    ha3 ham haLeaf hc3 hcm hcLeaf
  have hSecond := finiteTwoBlockCarrier_right_leaf_oneType_iff
    FH FK hshape bits l b d hl3
    hb3 hbm hbLeaf hd3 hdm hdLeaf
  have hAux := finiteTwoBlockCarrier_right_pair_auxType_iff
    FH FK bits l a b c d hl3 hb3 hd3
  exact and_congr hFirst (and_congr hSecond hAux)

end DiaryLeafPriority
end ThreeUniformDiaries
