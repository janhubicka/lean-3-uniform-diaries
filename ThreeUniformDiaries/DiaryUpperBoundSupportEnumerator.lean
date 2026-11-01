import ThreeUniformDiaries.DiaryFiniteLeafMeetMarkerReindex

/-!
# Track B: genuine increasing extension of the finite support enumerator

The sorted finite support index is defined as zero outside its finite
domain. That is suitable for constructing a bounded induced graph,
but is NOT itself a globally strictly increasing map, so it cannot
be passed as the witness to the genuine finite ATR embedding API.

We extend the sorted enumerator by a tail strictly above every
old member of the finite support. Exactly the first S.card images
remain the literal sorted support; the tail is mathematical
bookkeeping and never participates in actual finite colours.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A total strictly increasing enumeration extending the genuine
sorted initial block of a finite support. -/
noncomputable def finiteSupportTotalEnum
    (S : Finset Nat) (i : Nat) : Nat :=
  if i < S.card then finiteSupportIndex S i
  else S.sup id + i + 1

/-- The first S.card values are the EXACT sorted support entries. -/
theorem finiteSupportTotalEnum_front
    (S : Finset Nat) (i : Nat) (hi : i < S.card) :
    finiteSupportTotalEnum S i = finiteSupportIndex S i := by
  simp only [finiteSupportTotalEnum, if_pos hi]

/-- The chosen tail is genuinely above the entire finite support,
not a second copy of a member of S. -/
theorem finiteSupportTotalEnum_tail_above
    (S : Finset Nat) (i : Nat) (hi : S.card ≤ i)
    (x : Nat) (hx : x ∈ S) :
    x < finiteSupportTotalEnum S i := by
  have hle : x ≤ S.sup id := by
    simpa only [id_eq] using
      (Finset.le_sup (f := id) hx)
  have hnot : ¬ i < S.card := by omega
  simp only [finiteSupportTotalEnum, if_neg hnot]
  omega

/-- Unlike finiteSupportIndex, this is strictly monotone on all
natural numbers, including at the finite/tail boundary. -/
theorem finiteSupportTotalEnum_strictMono
    (S : Finset Nat) :
    StrictMono (finiteSupportTotalEnum S) := by
  apply strictMono_nat_of_lt_succ
  intro i
  by_cases hnext : i + 1 < S.card
  · have hi : i < S.card := by omega
    simpa only [finiteSupportTotalEnum_front S i hi,
      finiteSupportTotalEnum_front S (i+1) hnext] using
      (finiteSupportIndex_strictMono S i (i+1) (by omega) hnext)
  · by_cases hi : i < S.card
    · have hx := finiteSupportIndex_mem S i hi
      have hbound := finiteSupportTotalEnum_tail_above
        S (i+1) (by omega) (finiteSupportIndex S i) hx
      rw [finiteSupportTotalEnum_front S i hi]
      exact hbound
    · have hinot : ¬ i < S.card := hi
      have hnextnot : ¬ i + 1 < S.card := by omega
      simp only [finiteSupportTotalEnum, if_neg hinot,
        if_neg hnextnot]
      omega

/-- The first three source markers remain literally fixed
whenever the support contains all three designated markers. -/
theorem finiteSupportTotalEnum_initial_markers
    (S : Finset Nat)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S) :
    finiteSupportTotalEnum S 0 = 0 ∧
    finiteSupportTotalEnum S 1 = 1 ∧
    finiteSupportTotalEnum S 2 = 2 := by
  obtain ⟨hCard,hZero,hOne,hTwo⟩ :=
    finiteSupportIndex_initial_markers S h0 h1 h2
  exact ⟨by simpa only [finiteSupportTotalEnum_front S 0 (by omega)]
      using hZero,
    by simpa only [finiteSupportTotalEnum_front S 1 (by omega)]
      using hOne,
    by simpa only [finiteSupportTotalEnum_front S 2 (by omega)]
      using hTwo⟩

/-- Exact edge and nonedge reflection on every genuine triple of
the compressed finite graph. The irrelevant infinite tail is
NOT part of the induced finite embedding claim. -/
theorem finiteSupportTotalEnum_edge_iff
    (G : Ordered3Graph Nat) (S : Finset Nat)
    (a b c : Nat) (hab : a < b) (hbc : b < c)
    (hc : c < S.card) :
    ((finiteSupportGraph G S).edge a b c ↔
      G.edge (finiteSupportTotalEnum S a)
        (finiteSupportTotalEnum S b)
        (finiteSupportTotalEnum S c)) := by
  have ha : a < S.card := by omega
  have hb : b < S.card := by omega
  simpa only [finiteSupportTotalEnum_front S a ha,
    finiteSupportTotalEnum_front S b hb,
    finiteSupportTotalEnum_front S c hc] using
    (finiteSupportGraph_edge_iff G S a b c hab hbc hc)

end DiaryLeafPriority
end ThreeUniformDiaries
