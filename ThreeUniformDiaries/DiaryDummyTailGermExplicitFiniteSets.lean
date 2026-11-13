import ThreeUniformDiaries.DiaryDummyTailFiniteRealisedGermCensus

/-!
# Track B: explicit finite Finset census for globally realised dummy-tail germs

The previous exact iff classification of realised singleton and full
pair germs in a countable dummy-tail carrier is now packaged as
literal equality with computably bounded finite sets. This removes
the existential search over the entire infinite dummy tail from
the ACTUAL realised-germ API at every old m<n.

The singleton set uses the genuine old leaf ranks in [m,n) plus
one new tail representative n. The full pair set uses:
  (a) genuine ordered pairs of old leaves in [m,n);
  (b) each genuine old leaf a in [m,n) paired with tail n;
  (c) one pure tail pair (n,n+1).

All type codes are the actual old-cut oneGermCode/twoGermCode
of the verified concrete carrier, with its real finite cross
marker orientation bits. The finite sets are noncomputable at
the Lean level because the arbitrary source edge predicate is
Prop-valued; their cardinality and membership are still
genuinely FINITE formulas, not independent compactness data.

The remaining compatibility problem is determining which
orientations make the selected one and two germ sets empty at
a prescribed protected old cut. No such orientation theorem
or relative strong absorber extension is claimed here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Literal finite set of possible singleton germs below an old
cut of a dummy-tail extension: all old leaf representatives plus
the ONE normal tail representative at n. -/
noncomputable def finiteDummyTailOneGermCensus
    (H : Ordered3Graph Nat) (n : Nat) (bits : Nat → Bool)
    (m : Nat) : Finset (OneGermSpace m) := by
  classical
  let T := finiteDummyTailCarrier H n bits
  let L := (Finset.Ico m n).filter (fun u => IsLeaf H u)
  exact L.image (fun u => oneGermCode T m u) ∪
    {oneGermCode T m n}

/-- Literal finite set of possible full ordered-pair germs below
an old cut: old-old pairs, one old-first/tail-second germ per
old leaf, and exactly one pure-tail ordered pair germ. -/
noncomputable def finiteDummyTailTwoGermCensus
    (H : Ordered3Graph Nat) (n : Nat) (bits : Nat → Bool)
    (m : Nat) : Finset (TwoGermSpace m) := by
  classical
  let T := finiteDummyTailCarrier H n bits
  let L := (Finset.Ico m n).filter (fun u => IsLeaf H u)
  exact ((L.product L).filter (fun q => q.1 < q.2)).image
        (fun q => twoGermCode T m q.1 q.2) ∪
      (L.image (fun a => twoGermCode T m a n) ∪
        {twoGermCode T m n (n+1)})

/-- For any genuine bounded finite source frame, the ACTUAL
globally realised singleton germ Finset of the countable
dummy-tail carrier is precisely the explicit finite census. -/
theorem finiteDummyTail_realisedOneGerms_eq_finiteCensus
    (H : Ordered3Graph Nat) (n : Nat)
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool) (m : Nat) (hm : m < n) :
    realisedOneGerms (finiteDummyTailCarrier H n bits) m =
      finiteDummyTailOneGermCensus H n bits m := by
  classical
  let T := finiteDummyTailCarrier H n bits
  apply Finset.ext
  intro g
  have hCensus :=
    finiteDummyTail_realisedOneGerms_oldCut_census
      H n FH bits m hm g
  constructor
  · intro hg
    rcases hCensus.mp hg with
      ⟨u,hmu,hun,hLeaf,hCode⟩ | hTail
    · change g ∈ ((Finset.Ico m n).filter (fun u => IsLeaf H u)).image
          (fun u => oneGermCode T m u) ∪
        {oneGermCode T m n}
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_image.mpr
        ⟨u,Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨hmu,hun⟩,hLeaf⟩,hCode⟩
    · change g ∈ ((Finset.Ico m n).filter (fun u => IsLeaf H u)).image
          (fun u => oneGermCode T m u) ∪
        {oneGermCode T m n}
      exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_singleton.mpr hTail))
  · intro h
    change g ∈ ((Finset.Ico m n).filter (fun u => IsLeaf H u)).image
          (fun u => oneGermCode T m u) ∪
        {oneGermCode T m n} at h
    rcases Finset.mem_union.mp h with hOld | hTail
    · obtain ⟨u,hu,hCode⟩ := Finset.mem_image.mp hOld
      obtain ⟨huRange,hLeaf⟩ := Finset.mem_filter.mp hu
      obtain ⟨hmu,hun⟩ := Finset.mem_Ico.mp huRange
      exact hCensus.mpr (Or.inl ⟨u,hmu,hun,hLeaf,hCode⟩)
    · exact hCensus.mpr
        (Or.inr (Finset.mem_singleton.mp hTail))

/-- The ACTUAL globally realised full pair-germ Finset of the
infinite dummy-tail carrier is exactly the explicit finite
old-old / old-tail / pure-tail representative census. -/
theorem finiteDummyTail_realisedTwoGerms_eq_finiteCensus
    (H : Ordered3Graph Nat) (n : Nat)
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool) (m : Nat) (hm : m < n) :
    realisedTwoGerms (finiteDummyTailCarrier H n bits) m =
      finiteDummyTailTwoGermCensus H n bits m := by
  classical
  let T := finiteDummyTailCarrier H n bits
  let L := (Finset.Ico m n).filter (fun u => IsLeaf H u)
  let Old : Finset (TwoGermSpace m) :=
    ((L.product L).filter (fun q => q.1 < q.2)).image
      (fun q => twoGermCode T m q.1 q.2)
  let Cross : Finset (TwoGermSpace m) :=
    L.image (fun a => twoGermCode T m a n)
  let Tail : Finset (TwoGermSpace m) :=
    {twoGermCode T m n (n+1)}
  have hExpand :
      finiteDummyTailTwoGermCensus H n bits m =
        Old ∪ (Cross ∪ Tail) := rfl
  apply Finset.ext
  intro g
  have hCensus :=
    finiteDummyTail_realisedTwoGerms_oldCut_census
      H n FH bits m hm g
  rw [hExpand]
  constructor
  · intro hg
    rcases hCensus.mp hg with
      ⟨a,b,hma,hab,hbn,hLa,hLb,hCode⟩ |
      ⟨a,hma,han,hLa,hCode⟩ | hTail
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_image.mpr
      have haL : a ∈ L := Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨hma,by omega⟩,hLa⟩
      have hbL : b ∈ L := Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨by omega,hbn⟩,hLb⟩
      exact ⟨(a,b),Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨haL,hbL⟩,hab⟩,hCode⟩
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_image.mpr
        ⟨a,Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨hma,han⟩,hLa⟩,hCode⟩
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_union.mpr
          (Or.inr (Finset.mem_singleton.mpr hTail))))
  · intro hg
    rcases Finset.mem_union.mp hg with hOld | hLater
    · obtain ⟨⟨a,b⟩,habIn,hCode⟩ := Finset.mem_image.mp hOld
      obtain ⟨hAB,hab⟩ := Finset.mem_filter.mp habIn
      obtain ⟨haL,hbL⟩ := Finset.mem_product.mp hAB
      obtain ⟨hRangeA,hLa⟩ := Finset.mem_filter.mp haL
      obtain ⟨hRangeB,hLb⟩ := Finset.mem_filter.mp hbL
      obtain ⟨hma,han⟩ := Finset.mem_Ico.mp hRangeA
      obtain ⟨_hmb,hbn⟩ := Finset.mem_Ico.mp hRangeB
      exact hCensus.mpr
        (Or.inl ⟨a,b,hma,hab,hbn,hLa,hLb,hCode⟩)
    · rcases Finset.mem_union.mp hLater with hCross | hTail
      · obtain ⟨a,haL,hCode⟩ := Finset.mem_image.mp hCross
        obtain ⟨hRange,hLa⟩ := Finset.mem_filter.mp haL
        obtain ⟨hma,han⟩ := Finset.mem_Ico.mp hRange
        exact hCensus.mpr
          (Or.inr (Or.inl ⟨a,hma,han,hLa,hCode⟩))
      · exact hCensus.mpr
          (Or.inr (Or.inr (Finset.mem_singleton.mp hTail)))

end DiaryLeafPriority
end ThreeUniformDiaries
