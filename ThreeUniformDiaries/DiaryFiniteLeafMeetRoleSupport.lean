import ThreeUniformDiaries.DiaryFiniteLeafMeetSupport

/-!
# Role purity and witnesses of finite leaf-meet supports

The finite support generated from genuine leaves of a countable
RoleDiary includes three markers, the selected leaves, their
distinct singleton meets, and full meets of genuinely ordered
selected leaf pairs. These additions have exact marker-defined
diary roles: singleton generators are one-splits, while each
full pair generator is marker one, a leaf cap, or a two-split.

In particular, any one-split retained by the generated finite
support was generated as a one-meet of two selected leaves;
any two-split was generated as a full meet of two ordered
selected leaf pairs. Thus every selected split has witnesses
among the selected leaves. The proof does not claim that the
induced support has already been reindexed into a finite diary.
That later step must also preserve the first disagreement at
the split, and all source-copy mixed meets.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {G : Ordered3Graph Nat} {L : Finset Nat}

/-- Every singleton generator of distinct selected leaves is
a genuine one-split in the ambient complete diary. -/
theorem finiteOneMeetSupport_isOneSplit
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    {m : Nat} (hm : m ∈ finiteOneMeetSupport G L) :
    IsOneSplit G m := by
  classical
  change m ∈ ((L.product L).filter
    (fun p : Nat × Nat => p.1 ≠ p.2)).image
      (fun p : Nat × Nat => G.oneMeetLevel p.1 p.2) at hm
  obtain ⟨p,hp,hpm⟩ := Finset.mem_image.mp hm
  rcases p with ⟨a,b⟩
  change G.oneMeetLevel a b = m at hpm
  obtain ⟨hp,hab⟩ := Finset.mem_filter.mp hp
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
  rw [← hpm]
  exact D.singleton_meets a b (hLeaves a ha) (hLeaves b hb) hab

/-- Every full pair-meet generator is marker one, a selected
leaf (the capped case), or a genuine two-split. No artificial
one-splits can enter through full pair meet generation. -/
theorem finiteTwoMeetSupport_role
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    {m : Nat} (hm : m ∈ finiteTwoMeetSupport G L) :
    m = 1 ∨ IsLeaf G m ∨ IsTwoSplit G m := by
  classical
  change m ∈
    ((finiteOrderedLeafPairs L).product (finiteOrderedLeafPairs L)).image
      (fun p : (Nat × Nat) × (Nat × Nat) =>
        G.twoMeetLevel p.1.1 p.1.2 p.2.1 p.2.2) at hm
  obtain ⟨p,hp,hpm⟩ := Finset.mem_image.mp hm
  rcases p with ⟨⟨a,b⟩,⟨c,d⟩⟩
  change G.twoMeetLevel a b c d = m at hpm
  obtain ⟨habP,hcdP⟩ := Finset.mem_product.mp hp
  obtain ⟨habMem,hab⟩ := Finset.mem_filter.mp habP
  obtain ⟨hcdMem,hcd⟩ := Finset.mem_filter.mp hcdP
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp habMem
  obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcdMem
  rcases D.pair_meets a b c d hab hcd
      (hLeaves a ha) (hLeaves b hb)
      (hLeaves c hc) (hLeaves d hd) with
    hCap | hOne | hTwo
  · have hMinLeaf : IsLeaf G (min a c) := by
      rcases le_total a c with hac | hca
      · rw [min_eq_left hac]
        exact hLeaves a ha
      · rw [min_eq_right hca]
        exact hLeaves c hc
    right
    left
    have hmCap : m = min a c := hpm.symm.trans hCap
    simpa only [hmCap] using hMinLeaf
  · left
    exact hpm.symm.trans hOne
  · right
    right
    rw [← hpm]
    exact hTwo

/-- All support vertices are old genuine diary roles or the
three initial markers. This is the role-purity condition needed
before finite increasing reindexing. -/
theorem finiteLeafMeetSupport_role
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    {m : Nat} (hm : m ∈ finiteLeafMeetSupport G L) :
    m < 3 ∨ IsLeaf G m ∨ IsOneSplit G m ∨ IsTwoSplit G m := by
  change m ∈ (Finset.range 3 ∪ L) ∪
    (finiteOneMeetSupport G L ∪ finiteTwoMeetSupport G L) at hm
  rcases Finset.mem_union.mp hm with hFront | hMeets
  · rcases Finset.mem_union.mp hFront with hMarker | hLeaf
    · exact Or.inl (Finset.mem_range.mp hMarker)
    · exact Or.inr (Or.inl (hLeaves m hLeaf))
  · rcases Finset.mem_union.mp hMeets with hOne | hTwo
    · exact Or.inr (Or.inr (Or.inl
        (finiteOneMeetSupport_isOneSplit D hLeaves hOne)))
    · rcases finiteTwoMeetSupport_role D hLeaves hTwo with
        hMarker | hLeaf | hSplit
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl hLeaf)
      · exact Or.inr (Or.inr (Or.inr hSplit))

/-- If a selected support vertex is a genuine one-split,
it must occur among the generated singleton meet levels. -/
theorem finiteLeafMeetSupport_oneSplit_generator
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    {m : Nat}
    (hm : m ∈ finiteLeafMeetSupport G L)
    (hOne : IsOneSplit G m) :
    m ∈ finiteOneMeetSupport G L := by
  change m ∈ (Finset.range 3 ∪ L) ∪
    (finiteOneMeetSupport G L ∪ finiteTwoMeetSupport G L) at hm
  rcases Finset.mem_union.mp hm with hFront | hMeets
  · rcases Finset.mem_union.mp hFront with hMarker | hLeaf
    · have hmSmall := Finset.mem_range.mp hMarker
      have hmLarge : 3 ≤ m := hOne.1
      omega
    · have hLeafRole := hLeaves m hLeaf
      exact False.elim (hLeafRole.2.1 hOne.2.1)
  · rcases Finset.mem_union.mp hMeets with hSelf | hTwo
    · exact hSelf
    · rcases finiteTwoMeetSupport_role D hLeaves hTwo with
        hMarker | hLeaf | hSplit
      · have hmLarge : 3 ≤ m := hOne.1
        omega
      · exact False.elim (hLeaf.2.1 hOne.2.1)
      · exact False.elim (hOne.2.2 hSplit.2.2)

/-- A genuine two-split in the generated support must arise as
the full meet of two ordered selected leaf pairs. -/
theorem finiteLeafMeetSupport_twoSplit_generator
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    {m : Nat}
    (hm : m ∈ finiteLeafMeetSupport G L)
    (hTwo : IsTwoSplit G m) :
    m ∈ finiteTwoMeetSupport G L := by
  change m ∈ (Finset.range 3 ∪ L) ∪
    (finiteOneMeetSupport G L ∪ finiteTwoMeetSupport G L) at hm
  rcases Finset.mem_union.mp hm with hFront | hMeets
  · rcases Finset.mem_union.mp hFront with hMarker | hLeaf
    · have hmSmall := Finset.mem_range.mp hMarker
      have hmLarge : 3 ≤ m := hTwo.1
      omega
    · have hLeafRole := hLeaves m hLeaf
      exact False.elim (hLeafRole.2.2 hTwo.2.2)
  · rcases Finset.mem_union.mp hMeets with hOne | hSelf
    · have hOneRole := finiteOneMeetSupport_isOneSplit D hLeaves hOne
      exact False.elim (hTwo.2.1 hOneRole.2.1)
    · exact hSelf

/-- Every selected one-split has genuine selected leaf witnesses
for its exact ambient singleton meet. -/
theorem finiteLeafMeetSupport_oneSplit_selected_witness
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    {m : Nat}
    (hm : m ∈ finiteLeafMeetSupport G L)
    (hOne : IsOneSplit G m) :
    ∃ a b : Nat, a ∈ L ∧ b ∈ L ∧
      a ≠ b ∧ G.oneMeetLevel a b = m := by
  classical
  have hGen := finiteLeafMeetSupport_oneSplit_generator
    D hLeaves hm hOne
  change m ∈ ((L.product L).filter
    (fun p : Nat × Nat => p.1 ≠ p.2)).image
      (fun p : Nat × Nat => G.oneMeetLevel p.1 p.2) at hGen
  obtain ⟨p,hp,hpm⟩ := Finset.mem_image.mp hGen
  rcases p with ⟨a,b⟩
  change G.oneMeetLevel a b = m at hpm
  obtain ⟨hp,hab⟩ := Finset.mem_filter.mp hp
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
  exact ⟨a,b,ha,hb,hab,hpm⟩

/-- Every selected two-split has genuine selected ordered pair
witnesses for its exact ambient full two-meet. -/
theorem finiteLeafMeetSupport_twoSplit_selected_witness
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    {m : Nat}
    (hm : m ∈ finiteLeafMeetSupport G L)
    (hTwo : IsTwoSplit G m) :
    ∃ a b c d : Nat,
      a ∈ L ∧ b ∈ L ∧ c ∈ L ∧ d ∈ L ∧
      a < b ∧ c < d ∧
      G.twoMeetLevel a b c d = m := by
  classical
  have hGen := finiteLeafMeetSupport_twoSplit_generator
    D hLeaves hm hTwo
  change m ∈
    ((finiteOrderedLeafPairs L).product (finiteOrderedLeafPairs L)).image
      (fun p : (Nat × Nat) × (Nat × Nat) =>
        G.twoMeetLevel p.1.1 p.1.2 p.2.1 p.2.2) at hGen
  obtain ⟨p,hp,hpm⟩ := Finset.mem_image.mp hGen
  rcases p with ⟨⟨a,b⟩,⟨c,d⟩⟩
  change G.twoMeetLevel a b c d = m at hpm
  obtain ⟨habP,hcdP⟩ := Finset.mem_product.mp hp
  obtain ⟨habMem,hab⟩ := Finset.mem_filter.mp habP
  obtain ⟨hcdMem,hcd⟩ := Finset.mem_filter.mp hcdP
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp habMem
  obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcdMem
  exact ⟨a,b,c,d,ha,hb,hc,hd,hab,hcd,hpm⟩

end DiaryLeafPriority
end ThreeUniformDiaries
