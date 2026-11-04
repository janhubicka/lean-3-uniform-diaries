import ThreeUniformDiaries.DiaryFiniteLeafMeetMarkerReindex

/-!
# Finite supports retaining an entire initial prefix

The canonical increasing enumeration of a finite support S literally
fixes every numerical coordinate i < b if [0,b) is contained in S.
Consequently the induced finite support graph agrees with the original
graph on the WHOLE bounded initial prefix, not merely on the selected
leaf/split generators.

This is a first step towards proving that every individual finite
canonical diary support admits an order-reserved embedding into a
prescribed generic leaf copy: use a LARGER full finite support that
retains all intervening source coordinates. Independent existence of
reserved finite maps still does NOT give a coherent countable family.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A retained full initial segment has the same indices in the
increasing enumeration of any larger finite support. -/
theorem finiteSupportIndex_eq_self_of_range_subset
    (S : Finset Nat) (b : Nat)
    (hPrefix : Finset.range b ⊆ S)
    (i : Nat) (hi : i < b) :
    finiteSupportIndex S i = i := by
  classical
  induction i using Nat.strong_induction_on with
  | h i ih =>
    have hiS : i ∈ S :=
      hPrefix (Finset.mem_range.mpr hi)
    obtain ⟨j,hj,hji⟩ :=
      finiteSupportIndex_surjective_on S i hiS
    have hjle : j ≤ i := by
      have := finiteSupportIndex_ge_index S j hj
      omega
    have hjiEq : j = i := by
      by_contra hne
      have hjlt : j < i := by omega
      have hjb : j < b := by omega
      have hEarlier := ih j hjlt hjb
      omega
    simpa only [hjiEq] using hji

/-- If [0,b) is retained, its length does not exceed the support
cardinality (needed to apply the induced graph edge interface). -/
theorem cardinality_ge_of_prefix_subset
    (S : Finset Nat) (b : Nat)
    (hPrefix : Finset.range b ⊆ S) :
    b ≤ S.card := by
  have h := Finset.card_le_card hPrefix
  simpa only [Finset.card_range] using h

/-- No triple or nontriple with coordinates below b changes when
a larger finite diary support is reindexed. -/
theorem finiteSupportGraph_edge_prefix_iff
    (G : Ordered3Graph Nat) (S : Finset Nat) (b : Nat)
    (hPrefix : Finset.range b ⊆ S)
    (x y z : Nat) (hxy : x < y) (hyz : y < z)
    (hzb : z < b) :
    (finiteSupportGraph G S).edge x y z ↔ G.edge x y z := by
  have hbCard : b ≤ S.card :=
    cardinality_ge_of_prefix_subset S b hPrefix
  have hxB : x < b := by omega
  have hyB : y < b := by omega
  rw [finiteSupportGraph_edge_iff G S x y z hxy hyz (by omega)]
  rw [finiteSupportIndex_eq_self_of_range_subset S b hPrefix x hxB,
    finiteSupportIndex_eq_self_of_range_subset S b hPrefix y hyB,
    finiteSupportIndex_eq_self_of_range_subset S b hPrefix z hzb]

end DiaryLeafPriority
end ThreeUniformDiaries
