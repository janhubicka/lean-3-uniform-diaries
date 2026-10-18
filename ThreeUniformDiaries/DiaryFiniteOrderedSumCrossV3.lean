import ThreeUniformDiaries.DiaryFiniteOrderedSumOrientationChoice

/-!
# Complete cross Devlin V3 through a causal orientation

The raw two-block carrier admits cross edges only of the two
Devlin marker shapes, with exactly complementary Boolean bits.
The finite causal orientation construction then ensures both
literal Devlin V3 equivalences for every cross-block leaf pair,
even when the right block has no leaves (a vacuous case).

No assertion of the global pre-diary, protected meets, finite
diary output or every-flip absorption is made.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- Cross marker 2 reflects exactly the FALSE orientation bit. -/
theorem finiteTwoBlockCarrier_cross_marker_two
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (u v : Nat) (hu3 : 3 ≤ u) (hun : u < n)
    (huLeaf : IsLeaf H u) (hv3 : 3 ≤ v) (hvm : v < m)
    (hvLeaf : IsLeaf K v) :
    (finiteTwoBlockCarrier H K n m bits).edge
      2 u (rightBlockImage n v) ↔ bits u = false := by
  constructor
  · intro he
    rcases he with hLeft | hRight | hCross
    · have hge := rightBlockImage_nonmarker_ge n v
        FH.length_ge_three hv3
      omega
    · obtain ⟨a,b,c,hK,_hc,ha,hb,_hz⟩ := hRight
      have hbImage : rightBlockImage n b = u := hb.symm
      by_cases hb3 : 3 ≤ b
      · have hge := rightBlockImage_nonmarker_ge n b
          FH.length_ge_three hb3
        omega
      · have hbSmall : b < 3 := by omega
        rw [rightBlockImage_marker n b hbSmall] at hbImage
        omega
    · obtain ⟨u',v',_hu3,_hun,_hlu,_hv3,_hvm,_hlv,hy,hz,hBit⟩ := hCross
      have hu : u' = u := hy.symm
      subst u'
      rcases hBit with hOne | hTwo
      · omega
      · exact hTwo.2
  · intro hFalse
    exact Or.inr (Or.inr
      ⟨u,v,hu3,hun,huLeaf,hv3,hvm,hvLeaf,
        rfl,rfl,Or.inr ⟨rfl,hFalse⟩⟩)

/-- Both cross-marker incidences are literally complementary. -/
theorem finiteTwoBlockCarrier_cross_marker_complement
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (u v : Nat) (hu3 : 3 ≤ u) (hun : u < n)
    (huLeaf : IsLeaf H u) (hv3 : 3 ≤ v) (hvm : v < m)
    (hvLeaf : IsLeaf K v) :
    ((finiteTwoBlockCarrier H K n m bits).edge
        2 u (rightBlockImage n v) ↔
      ¬ (finiteTwoBlockCarrier H K n m bits).edge
        1 u (rightBlockImage n v)) := by
  have hOne :=
    finiteTwoBlockCarrier_cross_marker_one
      FH FK bits u v hu3 hun huLeaf hv3 hvm hvLeaf
  have hTwo :=
    finiteTwoBlockCarrier_cross_marker_two
      FH FK bits u v hu3 hun huLeaf hv3 hvm hvLeaf
  have hBool : (bits u = false) ↔ ¬ (bits u = true) := by
    cases h : bits u <;> simp [h]
  exact hTwo.trans (hBool.trans (not_congr hOne.symm))

/-- A single ACTUAL orientation solves BOTH cross-copy V3 equations
for every left and right leaf. The empty-right-leaf case is vacuous. -/
theorem exists_finiteTwoBlockOrientation_cross_V3_both
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hshape : ∀ a b c : Nat, K.edge a b c →
      PermittedDiaryEdge K a b c) :
    ∃ bits : Nat → Bool,
      ∀ u v : Nat, 3 ≤ u → u < n → IsLeaf H u →
        3 ≤ v → v < m → IsLeaf K v →
        (((finiteTwoBlockCarrier H K n m bits).edge
            1 u (rightBlockImage n v) ↔
          LexEarlier (finiteTwoBlockCarrier H K n m bits)
            u (rightBlockImage n v)) ∧
         ((finiteTwoBlockCarrier H K n m bits).edge
            2 u (rightBlockImage n v) ↔
          ¬ LexEarlier (finiteTwoBlockCarrier H K n m bits)
            u (rightBlockImage n v))) := by
  classical
  by_cases hExists : ∃ v0 : Nat, 3 ≤ v0 ∧ v0 < m ∧ IsLeaf K v0
  · obtain ⟨v0,hv03,hv0m,hv0Leaf⟩ := hExists
    obtain ⟨bits,hOne⟩ :=
      exists_finiteTwoBlockOrientation_cross_V3_one
        FH FK hshape v0 hv03 hv0m hv0Leaf
    refine ⟨bits, ?_⟩
    intro u v hu3 hun huLeaf hv3 hvm hvLeaf
    have hOneUV :=
      hOne u v hu3 hun huLeaf hv3 hvm hvLeaf
    have hComplement :=
      finiteTwoBlockCarrier_cross_marker_complement
        FH FK bits u v hu3 hun huLeaf hv3 hvm hvLeaf
    exact ⟨hOneUV, hComplement.trans (not_congr hOneUV)⟩
  · refine ⟨fun _ => false, ?_⟩
    intro u v hu3 hun huLeaf hv3 hvm hvLeaf
    exact False.elim (hExists ⟨v,hv3,hvm,hvLeaf⟩)

end DiaryLeafPriority
end ThreeUniformDiaries
