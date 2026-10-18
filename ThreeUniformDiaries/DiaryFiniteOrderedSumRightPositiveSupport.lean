import ThreeUniformDiaries.DiaryFiniteOrderedSumRightCoherence

/-!
# All positive incidences at translated right splits come from the right block

The right-block coherence lemmas already treat genuine translated
right leaf images. To apply them to ALL positive target classes,
we first need to prove that a split in the translated right block
cannot acquire an additional positive leaf or pair from another
block. This follows directly from the three disjuncts of the
finite carrier edge definition.

Both support theorems below are exact, two-sided *source recovery*
statements. They make no positive target V1/V2 coherence assumption,
and require no source V/E/S axioms beyond finite ordered edge support.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- A target incidence (0,rightSplit,a) at an actual right nonmarker
s comes from a genuine K-edge (0,s,c). In particular its endpoint
is a translated right vertex, never an unrelated left or cross leaf. -/
theorem finiteTwoBlockCarrier_right_oneSplit_positive_source
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (s a : Nat) (hs3 : 3 ≤ s) (hsm : s < m)
    (hPos : (finiteTwoBlockCarrier H K n m bits).edge
      0 (rightBlockImage n s) a) :
    ∃ c : Nat, c < m ∧ a = rightBlockImage n c ∧ K.edge 0 s c := by
  have hn3 : 3 ≤ n := FH.length_ge_three
  have hSn : n ≤ rightBlockImage n s :=
    rightBlockImage_nonmarker_ge n s hn3 hs3
  have hinj := (rightBlockImage_strictMono n hn3).injective
  rcases hPos with hLeft | hRight | hCross
  · have ho := FH.edge_support 0 (rightBlockImage n s) a hLeft.1
    omega
  · obtain ⟨a',b',c',hK,hcm,hFirst,hMiddle,hLast⟩ := hRight
    have hZero : rightBlockImage n 0 = 0 :=
      rightBlockImage_marker n 0 (by omega)
    have ha0 : a' = 0 := hinj (by
      calc
        rightBlockImage n a' = 0 := hFirst.symm
        _ = rightBlockImage n 0 := hZero.symm)
    have hbS : b' = s := hinj hMiddle.symm
    subst a'
    subst b'
    exact ⟨c',hcm,hLast,hK⟩
  · obtain ⟨u,v,hu3,hun,huLeaf,hv3,hvm,hvLeaf,
        hMiddle,hLast,hBit⟩ := hCross
    omega

/-- A target incidence (rightSplit,a,b) at an actual right
nonmarker s comes from a genuine source right edge (s,c,d),
and BOTH pair members are translated right vertices. -/
theorem finiteTwoBlockCarrier_right_twoSplit_positive_source
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (s a b : Nat) (hs3 : 3 ≤ s) (hsm : s < m)
    (hPos : (finiteTwoBlockCarrier H K n m bits).edge
      (rightBlockImage n s) a b) :
    ∃ c d : Nat, c < m ∧ d < m ∧
      a = rightBlockImage n c ∧ b = rightBlockImage n d ∧
      K.edge s c d := by
  have hn3 : 3 ≤ n := FH.length_ge_three
  have hSn : n ≤ rightBlockImage n s :=
    rightBlockImage_nonmarker_ge n s hn3 hs3
  have hinj := (rightBlockImage_strictMono n hn3).injective
  rcases hPos with hLeft | hRight | hCross
  · have ho :=
      FH.edge_support (rightBlockImage n s) a b hLeft.1
    omega
  · obtain ⟨a',b',c',hK,hcm,hFirst,hMiddle,hLast⟩ := hRight
    have hsSource : a' = s := hinj hFirst.symm
    subst a'
    have hbc : b' < c' := (FK.edge_support s b' c' hK).2.1
    refine ⟨b',c',?_,hcm,hMiddle,hLast,hK⟩
    omega
  · obtain ⟨u,v,hu3,hun,huLeaf,hv3,hvm,hvLeaf,
        hMiddle,hLast,hBit⟩ := hCross
    rcases hBit with hOne | hTwo
    · omega
    · omega

end DiaryLeafPriority
end ThreeUniformDiaries
