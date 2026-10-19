import ThreeUniformDiaries.DiaryFiniteDummyTailOldMeets

/-!
# Global marker roles and V1/V2 coherence of a countable dummy tail

The dummy tail adds NO edge with first coordinate zero and NO
edge with first coordinate an old nonmarker split. Consequently
it cannot create new leaves positively incident with a source
one-split, nor new ordered pairs incident with a source two-split.

All target splits are original finite splits; every vertex in
the tail is a leaf. Their marker-defined source/target roles
are reflected by the exact induced finite-prefix relation.

Using exact singleton and full pair-type transport of the old
finite vertices, both full V1 and V2 positive-class coherence
clauses remain valid in the countable carrier with unrestricted
quantification over ALL Nat. This uses no chosen cross V3 bits
and does not claim global V/E pre-diary yet.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat} {n : Nat}

/-- All three marker-role predicates are unchanged on each
original finite nonmarker vertex. -/
theorem finiteDummyTailCarrier_old_leaf_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (z : Nat) (hzn : z < n) :
    IsLeaf (finiteDummyTailCarrier H n bits) z ↔ IsLeaf H z := by
  have hM := finiteDummyTailCarrier_old_role_bits FH bits z hzn
  constructor
  · intro hz
    exact ⟨hz.1, fun he => hz.2.1 (hM.1.mpr he),
      fun he => hz.2.2 (hM.2.mpr he)⟩
  · intro hz
    exact ⟨hz.1, fun he => hz.2.1 (hM.1.mp he),
      fun he => hz.2.2 (hM.2.mp he)⟩

theorem finiteDummyTailCarrier_old_oneSplit_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (z : Nat) (hzn : z < n) :
    IsOneSplit (finiteDummyTailCarrier H n bits) z ↔ IsOneSplit H z := by
  have hM := finiteDummyTailCarrier_old_role_bits FH bits z hzn
  constructor
  · intro hz
    exact ⟨hz.1, hM.1.mp hz.2.1,
      fun he => hz.2.2 (hM.2.mpr he)⟩
  · intro hz
    exact ⟨hz.1, hM.1.mpr hz.2.1,
      fun he => hz.2.2 (hM.2.mp he)⟩

theorem finiteDummyTailCarrier_old_twoSplit_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (z : Nat) (hzn : z < n) :
    IsTwoSplit (finiteDummyTailCarrier H n bits) z ↔ IsTwoSplit H z := by
  have hM := finiteDummyTailCarrier_old_role_bits FH bits z hzn
  constructor
  · intro hz
    exact ⟨hz.1, fun he => hz.2.1 (hM.1.mpr he),
      hM.2.mp hz.2.2⟩
  · intro hz
    exact ⟨hz.1, fun he => hz.2.1 (hM.1.mp he),
      hM.2.mpr hz.2.2⟩

/-- Any genuine target one-split necessarily belongs to the
original finite source segment. -/
theorem finiteDummyTailCarrier_oneSplit_lt
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (s : Nat) (hs : IsOneSplit (finiteDummyTailCarrier H n bits) s) :
    s < n := by
  by_contra hbad
  have hsn : n ≤ s := by omega
  have hsLeaf := finiteDummyTailCarrier_tail_isLeaf FH bits s hsn
  exact hsLeaf.2.1 hs.2.1

/-- Any genuine target two-split is likewise an old finite
split; no dummy tail level has the two-split role marker. -/
theorem finiteDummyTailCarrier_twoSplit_lt
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (s : Nat) (hs : IsTwoSplit (finiteDummyTailCarrier H n bits) s) :
    s < n := by
  by_contra hbad
  have hsn : n ≤ s := by omega
  have hsLeaf := finiteDummyTailCarrier_tail_isLeaf FH bits s hsn
  exact hsLeaf.2.2 hs.2.2

/-- True GLOBAL role validity for the entire countable carrier,
given only the bounded source finite role coverage. -/
theorem finiteDummyTailCarrier_role_valid
    (P : FiniteRolePrediaryBlock H n)
    (bits : Nat → Bool) :
    ∀ z : Nat, 3 ≤ z →
      IsLeaf (finiteDummyTailCarrier H n bits) z ∨
      IsOneSplit (finiteDummyTailCarrier H n bits) z ∨
      IsTwoSplit (finiteDummyTailCarrier H n bits) z := by
  intro z hz3
  by_cases hzn : z < n
  · rcases P.role_valid z hz3 hzn with hLeaf | hOne | hTwo
    · exact Or.inl
        ((finiteDummyTailCarrier_old_leaf_iff
          P.frame bits z hzn).mpr hLeaf)
    · exact Or.inr (Or.inl
        ((finiteDummyTailCarrier_old_oneSplit_iff
          P.frame bits z hzn).mpr hOne))
    · exact Or.inr (Or.inr
        ((finiteDummyTailCarrier_old_twoSplit_iff
          P.frame bits z hzn).mpr hTwo))
  · exact Or.inl
      (finiteDummyTailCarrier_tail_isLeaf
        P.frame bits z (by omega))

/-- No dummy-tail edge with first marker zero can be new.
Every target (0,y,z) edge is literally an old source edge,
with its last endpoint inside the bounded original source. -/
theorem finiteDummyTailCarrier_zero_positive_source
    (bits : Nat → Bool)
    (y z : Nat)
    (he : (finiteDummyTailCarrier H n bits).edge 0 y z) :
    z < n ∧ H.edge 0 y z := by
  rcases he with hOld | hCross | hTail
  · exact ⟨hOld.2,hOld.1⟩
  · obtain ⟨u,_hu3,_hun,_huLeaf,_hz,_hy,hBit⟩ := hCross
    rcases hBit with hOne | hTwo
    · omega
    · omega
  · omega

/-- No dummy-tail edge with a nonmarker first vertex can be
new. In particular every positive edge at a two-split is old. -/
theorem finiteDummyTailCarrier_nonmarker_positive_source
    (bits : Nat → Bool)
    (x y z : Nat) (hx3 : 3 ≤ x)
    (he : (finiteDummyTailCarrier H n bits).edge x y z) :
    z < n ∧ H.edge x y z := by
  rcases he with hOld | hCross | hTail
  · exact ⟨hOld.2,hOld.1⟩
  · obtain ⟨u,_hu3,_hun,_huLeaf,_hz,_hy,hBit⟩ := hCross
    rcases hBit with hOne | hTwo
    · omega
    · omega
  · omega

/-- Complete V1 positive-class coherence at EVERY target
one-split, with all target leaves quantified without restrictions. -/
theorem finiteDummyTailCarrier_oneSplit_coherent
    (P : FiniteRolePrediaryBlock H n)
    (bits : Nat → Bool)
    (s a b : Nat)
    (hs : IsOneSplit (finiteDummyTailCarrier H n bits) s)
    (ha : IsLeaf (finiteDummyTailCarrier H n bits) a)
    (hb : IsLeaf (finiteDummyTailCarrier H n bits) b)
    (hA : (finiteDummyTailCarrier H n bits).edge 0 s a)
    (hB : (finiteDummyTailCarrier H n bits).edge 0 s b) :
    (finiteDummyTailCarrier H n bits).SameOneTypeBelow s a b := by
  have hsn := finiteDummyTailCarrier_oneSplit_lt P.frame bits s hs
  obtain ⟨han,hSourceA⟩ :=
    finiteDummyTailCarrier_zero_positive_source bits s a hA
  obtain ⟨hbn,hSourceB⟩ :=
    finiteDummyTailCarrier_zero_positive_source bits s b hB
  have hsSource : IsOneSplit H s :=
    (finiteDummyTailCarrier_old_oneSplit_iff
      P.frame bits s hsn).mp hs
  have haSource : IsLeaf H a :=
    (finiteDummyTailCarrier_old_leaf_iff
      P.frame bits a han).mp ha
  have hbSource : IsLeaf H b :=
    (finiteDummyTailCarrier_old_leaf_iff
      P.frame bits b hbn).mp hb
  exact (finiteDummyTailCarrier_old_oneType_iff
    P.frame bits s a b han hbn).mpr
      (P.one_split_coherent s a b hsSource
        haSource hbSource hSourceA hSourceB)

/-- Complete V2 coherence at EVERY target two-split and every
two genuinely positive ordered target leaf pairs. -/
theorem finiteDummyTailCarrier_twoSplit_coherent
    (P : FiniteRolePrediaryBlock H n)
    (bits : Nat → Bool)
    (s a b c d : Nat)
    (hs : IsTwoSplit (finiteDummyTailCarrier H n bits) s)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf (finiteDummyTailCarrier H n bits) a)
    (hb : IsLeaf (finiteDummyTailCarrier H n bits) b)
    (hc : IsLeaf (finiteDummyTailCarrier H n bits) c)
    (hd : IsLeaf (finiteDummyTailCarrier H n bits) d)
    (hAB : (finiteDummyTailCarrier H n bits).edge s a b)
    (hCD : (finiteDummyTailCarrier H n bits).edge s c d) :
    (finiteDummyTailCarrier H n bits).SameTwoTypeBelow s a b c d := by
  have hsn := finiteDummyTailCarrier_twoSplit_lt P.frame bits s hs
  obtain ⟨hbn,hSourceAB⟩ :=
    finiteDummyTailCarrier_nonmarker_positive_source
      bits s a b hs.1 hAB
  obtain ⟨hdn,hSourceCD⟩ :=
    finiteDummyTailCarrier_nonmarker_positive_source
      bits s c d hs.1 hCD
  have han : a < n := by omega
  have hcn : c < n := by omega
  have hsSource : IsTwoSplit H s :=
    (finiteDummyTailCarrier_old_twoSplit_iff
      P.frame bits s hsn).mp hs
  have haSource : IsLeaf H a :=
    (finiteDummyTailCarrier_old_leaf_iff P.frame bits a han).mp ha
  have hbSource : IsLeaf H b :=
    (finiteDummyTailCarrier_old_leaf_iff P.frame bits b hbn).mp hb
  have hcSource : IsLeaf H c :=
    (finiteDummyTailCarrier_old_leaf_iff P.frame bits c hcn).mp hc
  have hdSource : IsLeaf H d :=
    (finiteDummyTailCarrier_old_leaf_iff P.frame bits d hdn).mp hd
  exact (finiteDummyTailCarrier_old_twoType_iff
    P.frame bits s a b c d han hbn hcn hdn).mpr
      (P.two_split_coherent s a b c d hsSource
        hab hcd haSource hbSource hcSource hdSource
        hSourceAB hSourceCD)

end DiaryLeafPriority
end ThreeUniformDiaries
