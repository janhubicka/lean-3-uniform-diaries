import ThreeUniformDiaries.DiarySelectedCarrierClosure

/-!
# Minimal singleton/full-pair meet envelopes of pointed diary images

A finite selected carrier is the *least meet-closed* set containing
the entire protected prefix and the two distinguished leaves.
In the three-tail case any such set must also contain the split,
since it is the singleton meet of the leaves in the target.
This closes the set-theoretic minimality argument, conditionally on
a strictly increasing canonical enumeration of the selected vertices.

The closure notion includes the manuscript's full ordinary 2-type
meets, not only auxiliary pair meets. This module deliberately
separates minimal meet-closure from the implementation of the
canonical enumeration / minimal type-envelope data structure.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Intrinsic certificate of the least meet-closed set containing
a protected prefix and two endpoints. -/
def IsMinimalMeetEnvelope (K : Ordered3Graph Nat)
    (j a b : Nat) (S : Set Nat) : Prop :=
  K.IsMeetClosed S ∧
  (∀ t < j, t ∈ S) ∧
  a ∈ S ∧ b ∈ S ∧
  (∀ T : Set Nat, K.IsMeetClosed T →
    (∀ t < j, t ∈ T) → a ∈ T → b ∈ T → S ⊆ T)

/-- The selected two-tail carrier is already the smallest set
containing the entire prefix and the two chosen endpoints. -/
theorem two_tail_selectedCarrier_minimal
    (f : Nat → Nat) (j a b : Nat)
    (hfix : ∀ t < j, f t = t)
    (hfA : f j = a)
    (hfB : f (j+1) = b)
    (T : Set Nat)
    (hprefix : ∀ t < j, t ∈ T)
    (ha : a ∈ T) (hb : b ∈ T) :
    selectedCarrier f (j+2) ⊆ T := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := hx
  by_cases hpre : t < j
  · rw [hfix t hpre]
    exact hprefix t hpre
  · have hcase : t = j ∨ t = j+1 := by omega
    rcases hcase with h | h
    · simpa only [h, hfA] using ha
    · simpa only [h, hfB] using hb

/-- For three tails, closure under singleton meets forces the
split vertex: there are no other required generators. -/
theorem three_tail_selectedCarrier_minimal
    {H K : Ordered3Graph Nat}
    (ψ : Embedding H K) (hψ : ψ.TypeRespecting)
    (i m a b : Nat) (hmeet : H.oneMeetLevel a b = m)
    (f : Nat → Nat)
    (hfix : ∀ t < ψ i, f t = t)
    (hfM : f (ψ i) = ψ m)
    (hfA : f (ψ i + 1) = ψ a)
    (hfB : f (ψ i + 2) = ψ b)
    (T : Set Nat) (hclosed : K.IsMeetClosed T)
    (hprefix : ∀ t < ψ i, t ∈ T)
    (ha : ψ a ∈ T) (hb : ψ b ∈ T) :
    selectedCarrier f (ψ i+3) ⊆ T := by
  have hmeetImage : K.oneMeetLevel (ψ a) (ψ b) = ψ m := by
    simpa only [hmeet] using
      (typeRespecting_oneMeetLevel_eq ψ hψ a b)
  have hm : ψ m ∈ T := by
    simpa only [hmeetImage] using (hclosed.1 (ψ a) (ψ b) ha hb)
  intro x hx
  obtain ⟨t, ht, rfl⟩ := hx
  by_cases hpre : t < ψ i
  · rw [hfix t hpre]
    exact hprefix t hpre
  · have hcase : t = ψ i ∨ t = ψ i+1 ∨ t = ψ i+2 := by omega
    rcases hcase with h | h | h
    · simpa only [h, hfM] using hm
    · simpa only [h, hfA] using ha
    · simpa only [h, hfB] using hb

/-- Full minimal meet-closure for the two-tail case of a
type-respecting image, with all omitted target levels allowed. -/
theorem two_tail_minimalMeetEnvelope_after_type_embedding
    {H K : Ordered3Graph Nat}
    (ψ : Embedding H K) (hψ : ψ.TypeRespecting)
    (i a b : Nat) (hearly : H.oneMeetLevel a b < i)
    (f : Nat → Nat) (hf : StrictMono f)
    (hfix : ∀ t < ψ i, f t = t)
    (hfA : f (ψ i) = ψ a)
    (hfB : f (ψ i + 1) = ψ b) :
    K.IsMinimalMeetEnvelope (ψ i) (ψ a) (ψ b)
      (selectedCarrier f (ψ i+2)) := by
  obtain ⟨hone, haux⟩ :=
    two_tail_ATR_after_type_embedding ψ hψ i a b
      hearly f hf hfix hfA hfB
  refine ⟨K.selectedCarrier_meet_closed_of_ATR
      f hf (ψ i+2) hone haux, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨t, by omega, hfix t ht⟩
  · exact ⟨ψ i, by omega, hfA⟩
  · exact ⟨ψ i+1, by omega, hfB⟩
  · intro T hclosed hprefix ha hb
    exact two_tail_selectedCarrier_minimal f (ψ i) (ψ a) (ψ b)
      hfix hfA hfB T hprefix ha hb

/-- Full minimal meet-closure for the three-tail diary case.
The only source assumptions are the S1 split and E/V role shape.
No arbitrary mixed-pair auxiliary-meet transfer is assumed. -/
theorem role_three_tail_minimalMeetEnvelope_after_type_embedding
    {H K : Ordered3Graph Nat}
    (shape : DiaryLeafPriority.SplitEdgeShape H)
    (ψ : Embedding H K) (hψ : ψ.TypeRespecting)
    (i m a b : Nat)
    (hi : 3 ≤ i) (him : i ≤ m)
    (hm : DiaryLeafPriority.IsOneSplit H m)
    (ha : DiaryLeafPriority.IsLeaf H a)
    (hb : DiaryLeafPriority.IsLeaf H b)
    (hab : a < b) (hma : m < a)
    (hmeet : H.oneMeetLevel a b = m)
    (f : Nat → Nat) (hf : StrictMono f)
    (hfix : ∀ t < ψ i, f t = t)
    (hfM : f (ψ i) = ψ m)
    (hfA : f (ψ i+1) = ψ a)
    (hfB : f (ψ i+2) = ψ b) :
    K.IsMinimalMeetEnvelope (ψ i) (ψ a) (ψ b)
      (selectedCarrier f (ψ i+3)) := by
  obtain ⟨hone, haux⟩ :=
    DiaryLeafPriority.oneSplit_three_tail_ATR_after_type_embedding
      shape ψ hψ i m a b hi him hm ha hb hab hma hmeet
      f hf hfix hfM hfA hfB
  refine ⟨K.selectedCarrier_meet_closed_of_ATR
      f hf (ψ i+3) hone haux, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨t, by omega, hfix t ht⟩
  · exact ⟨ψ i+1, by omega, hfA⟩
  · exact ⟨ψ i+2, by omega, hfB⟩
  · intro T hclosed hprefix ha hb
    exact three_tail_selectedCarrier_minimal ψ hψ i m a b
      hmeet f hfix hfM hfA hfB T hclosed hprefix ha hb

end Ordered3Graph
end ThreeUniformDiaries
