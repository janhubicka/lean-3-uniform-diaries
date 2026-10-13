import ThreeUniformDiaries.DiaryRoleAxioms

/-!
# Full diary leaf-pair auxiliary transfer and small-envelope witnesses

The first theorem eliminates the artificial diary_cases input from
the previous transfer statement: the marker-edge formulation of
the diary axioms supplies it directly.

The second group proves quantitative auxiliary-meet bounds from
the precise edge-disagreement witnesses in a pointed leaf-pair
envelope. It does not yet formalise the entire ATR envelope inclusion.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

namespace RoleDiaryMeets

/-- A source diary's leaf-pair auxiliary meet is preserved by any
strictly increasing map preserving ordinary singleton and full
pair meets of the four leaves. Omitted target vertices are allowed.

This is the complete edge-derived transfer statement corresponding
to the second assertion of the manuscript's split-priority lemma. -/
theorem leaf_aux_transfer
    {H : Ordered3Graph Nat} (D : RoleDiaryMeets H)
    (K : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    {a b c d : Nat}
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hfull : K.twoMeetLevel (f a) (f b) (f c) (f d) =
      f (H.twoMeetLevel a b c d))
    (hfst : K.oneMeetLevel (f a) (f c) =
      f (H.oneMeetLevel a c))
    (hsnd : K.oneMeetLevel (f b) (f d) =
      f (H.oneMeetLevel b d)) :
    K.auxMeetLevel (f a) (f b) (f c) (f d) =
      f (H.auxMeetLevel a b c d) := by
  obtain ⟨hfirst, hfirstNotTwo⟩ := D.coordinate_meet_is_later ha hc
  obtain ⟨hsecond, hsecondNotTwo⟩ := D.coordinate_meet_is_later hb hd
  exact auxMeetLevel_preserved_of_diary_cases H K a b c d
    hab hcd (IsTwoSplit H)
    (D.pair a b c d hab hcd ha hb hc hd)
    hfirst hsecond hfirstNotTwo hsecondNotTwo
    f hf hfull hfst hsnd

end RoleDiaryMeets

/-- An auxiliary-type disagreement at vertex z forces
the corresponding auxiliary meet to be no later than z. -/
theorem auxMeetLevel_le_of_edge_disagreement
    (H : Ordered3Graph Nat) (u₀ u₁ v₀ v₁ z : Nat)
    (hdiff : ¬ (H.edge z u₀ u₁ ↔ H.edge z v₀ v₁)) :
    H.auxMeetLevel u₀ u₁ v₀ v₁ ≤ z := by
  by_contra hn
  have hz : z < H.auxMeetLevel u₀ u₁ v₀ v₁ := Nat.lt_of_not_ge hn
  exact hdiff ((H.auxMeetLevel_agree u₀ u₁ v₀ v₁) hz)

/-- The three pair auxiliary-meets of a pointed 1-split with its
two child leaves are all decided by the initial marker vertices.

The first disagreement comes from the two opposite successor
edges at vertex 0. Both other comparisons are separated by the
leaf-pair marker at vertex 1 or 2. -/
theorem split_leaf_triple_aux_bounds
    (H : Ordered3Graph Nat) (m a b : Nat)
    (hbranch : (H.edge 0 m a ∧ ¬ H.edge 0 m b) ∨
      (¬ H.edge 0 m a ∧ H.edge 0 m b))
    (hmarker : H.edge 1 a b ∨ H.edge 2 a b)
    (hno1a : ¬ H.edge 1 m a)
    (hno2a : ¬ H.edge 2 m a)
    (hno1b : ¬ H.edge 1 m b)
    (hno2b : ¬ H.edge 2 m b) :
    H.auxMeetLevel m a m b = 0 ∧
      H.auxMeetLevel m a a b ≤ 2 ∧
      H.auxMeetLevel m b a b ≤ 2 := by
  have hdiff0 : ¬ (H.edge 0 m a ↔ H.edge 0 m b) := by
    rcases hbranch with ⟨hea, hnb⟩ | ⟨hna, heb⟩
    · intro h
      exact hnb (h.mp hea)
    · intro h
      exact hna (h.mpr heb)
  have hzero : H.auxMeetLevel m a m b = 0 := by
    have hle := auxMeetLevel_le_of_edge_disagreement H m a m b 0 hdiff0
    omega
  have hboundA : H.auxMeetLevel m a a b ≤ 2 := by
    rcases hmarker with h1 | h2
    · have hd : ¬ (H.edge 1 m a ↔ H.edge 1 a b) := by
        intro h
        exact hno1a (h.mpr h1)
      have hle := auxMeetLevel_le_of_edge_disagreement H m a a b 1 hd
      omega
    · have hd : ¬ (H.edge 2 m a ↔ H.edge 2 a b) := by
        intro h
        exact hno2a (h.mpr h2)
      exact auxMeetLevel_le_of_edge_disagreement H m a a b 2 hd
  have hboundB : H.auxMeetLevel m b a b ≤ 2 := by
    rcases hmarker with h1 | h2
    · have hd : ¬ (H.edge 1 m b ↔ H.edge 1 a b) := by
        intro h
        exact hno1b (h.mpr h1)
      have hle := auxMeetLevel_le_of_edge_disagreement H m b a b 1 hd
      omega
    · have hd : ¬ (H.edge 2 m b ↔ H.edge 2 a b) := by
        intro h
        exact hno2b (h.mpr h2)
      exact auxMeetLevel_le_of_edge_disagreement H m b a b 2 hd
  exact ⟨hzero, hboundA, hboundB⟩

end DiaryLeafPriority
end ThreeUniformDiaries
