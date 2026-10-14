import ThreeUniformDiaries.DiaryThreeTailAuxTransfer
import ThreeUniformDiaries.DiarySingletonEnvelopeTransfer

/-!
# The finite ATR interface for pointed three-tail diary envelopes

In the image of a diary inside a generic 3-uniform hypergraph, the
three marker witnesses can lie at arbitrary positions inside the
protected target prefix. They are not necessarily at literal 0,1,2.

This module proves the correct shifted-marker inequalities and
assembles the already checked singleton and auxiliary compression
theorems. Its conclusion checks *every* meet comparison on the
finite pointed carrier. It does not assert that all ordinary type
envelopes of generic hypergraphs satisfy the required hypotheses.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- The three distinguished exterior pairs are separated before the
protected cut whenever their branch and leaf marker bits disagree at
(possibly shifted) vertices of that prefix. -/
theorem pointed_shifted_markers_early
    (H : Ordered3Graph Nat)
    (n z₀ z₁ z₂ m a b : Nat)
    (hz₀ : z₀ < n) (hz₁ : z₁ < n) (hz₂ : z₂ < n)
    (hbranch : (H.edge z₀ m a ∧ ¬ H.edge z₀ m b) ∨
      (¬ H.edge z₀ m a ∧ H.edge z₀ m b))
    (hmarker : H.edge z₁ a b ∨ H.edge z₂ a b)
    (hno₁a : ¬ H.edge z₁ m a)
    (hno₂a : ¬ H.edge z₂ m a)
    (hno₁b : ¬ H.edge z₁ m b)
    (hno₂b : ¬ H.edge z₂ m b) :
    H.auxMeetLevel m a m b < n ∧
      H.auxMeetLevel m a a b < n ∧
      H.auxMeetLevel m b a b < n := by
  have hdiff₀ : ¬ (H.edge z₀ m a ↔ H.edge z₀ m b) := by
    rcases hbranch with ⟨ha, hnb⟩ | ⟨hna, hb⟩
    · intro h
      exact hnb (h.mp ha)
    · intro h
      exact hna (h.mpr hb)
  have h₀ : H.auxMeetLevel m a m b < n :=
    lt_of_le_of_lt
      (ThreeUniformDiaries.DiaryLeafPriority.auxMeetLevel_le_of_edge_disagreement H m a m b z₀ hdiff₀) hz₀
  have h₁ : H.auxMeetLevel m a a b < n := by
    rcases hmarker with he | he
    · have hd : ¬ (H.edge z₁ m a ↔ H.edge z₁ a b) := by
        intro h
        exact hno₁a (h.mpr he)
      exact lt_of_le_of_lt
        (ThreeUniformDiaries.DiaryLeafPriority.auxMeetLevel_le_of_edge_disagreement H m a a b z₁ hd) hz₁
    · have hd : ¬ (H.edge z₂ m a ↔ H.edge z₂ a b) := by
        intro h
        exact hno₂a (h.mpr he)
      exact lt_of_le_of_lt
        (ThreeUniformDiaries.DiaryLeafPriority.auxMeetLevel_le_of_edge_disagreement H m a a b z₂ hd) hz₂
  have h₂ : H.auxMeetLevel m b a b < n := by
    rcases hmarker with he | he
    · have hd : ¬ (H.edge z₁ m b ↔ H.edge z₁ a b) := by
        intro h
        exact hno₁b (h.mpr he)
      exact lt_of_le_of_lt
        (ThreeUniformDiaries.DiaryLeafPriority.auxMeetLevel_le_of_edge_disagreement H m b a b z₁ hd) hz₁
    · have hd : ¬ (H.edge z₂ m b ↔ H.edge z₂ a b) := by
        intro h
        exact hno₂b (h.mpr he)
      exact lt_of_le_of_lt
        (ThreeUniformDiaries.DiaryLeafPriority.auxMeetLevel_le_of_edge_disagreement H m b a b z₂ hd) hz₂
  exact ⟨h₀, h₁, h₂⟩

/-- **Complete finite three-tail ATR interface.**

The carrier [0,n+3) consists of a protected full prefix and three
additional vertices, a first split and its two leaves. The first
split has early singleton meets with each leaf; the leaf-leaf meet
is exactly the split. Marker bits are retained in the protected
prefix. Then the canonical induced compression preserves all
singleton and auxiliary pair meets, even across omitted target
levels. -/
theorem pointed_three_tail_ATR_finite
    (H : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (n z₀ z₁ z₂ : Nat)
    (hfix : ∀ z, z < n → f z = z)
    (hz₀ : z₀ < n) (hz₁ : z₁ < n) (hz₂ : z₂ < n)
    (hone₀ : H.oneMeetLevel (f n) (f (n+1)) < n)
    (hone₁ : H.oneMeetLevel (f n) (f (n+2)) < n)
    (hleaf : H.oneMeetLevel (f (n+1)) (f (n+2)) = f n)
    (hbranch : (H.edge z₀ (f n) (f (n+1)) ∧
       ¬ H.edge z₀ (f n) (f (n+2))) ∨
      (¬ H.edge z₀ (f n) (f (n+1)) ∧
        H.edge z₀ (f n) (f (n+2))))
    (hmarker : H.edge z₁ (f (n+1)) (f (n+2)) ∨
      H.edge z₂ (f (n+1)) (f (n+2)))
    (hno₁a : ¬ H.edge z₁ (f n) (f (n+1)))
    (hno₂a : ¬ H.edge z₂ (f n) (f (n+1)))
    (hno₁b : ¬ H.edge z₁ (f n) (f (n+2)))
    (hno₂b : ¬ H.edge z₂ (f n) (f (n+2))) :
    (∀ u v, u < n+3 → v < n+3 →
      H.oneMeetLevel (f u) (f v) =
        f ((H.pullback f).oneMeetLevel u v)) ∧
    (∀ a b c d, a < b → c < d →
      b < n+3 → d < n+3 →
      H.auxMeetLevel (f a) (f b) (f c) (f d) =
        f ((H.pullback f).auxMeetLevel a b c d)) := by
  obtain ⟨haux₀, haux₁, haux₂⟩ :=
    H.pointed_shifted_markers_early n z₀ z₁ z₂
      (f n) (f (n+1)) (f (n+2))
      hz₀ hz₁ hz₂ hbranch hmarker
      hno₁a hno₂a hno₁b hno₂b
  have hbranchDiff :
      ¬ (H.edge z₀ (f n) (f (n+1)) ↔
        H.edge z₀ (f n) (f (n+2))) := by
    rcases hbranch with ⟨ha, hnb⟩ | ⟨hna, hb⟩
    · intro h
      exact hnb (h.mp ha)
    · intro h
      exact hna (h.mpr hb)
  have hwitness : ∃ z, z < n ∧
      ¬ (H.edge (f z) (f n) (f (n+1)) ↔
         H.edge (f z) (f n) (f (n+2))) := by
    refine ⟨z₀, hz₀, ?_⟩
    rw [hfix z₀ hz₀]
    exact hbranchDiff
  refine ⟨?_, ?_⟩
  · intro u v hu hv
    exact H.three_tail_oneMeet_preserved f hf n
      hfix hone₀ hone₁ hleaf hwitness u v hu hv
  · intro a b c d hab hcd hb hd
    exact H.three_tail_auxMeet_preserved f hf n
      hfix haux₀ haux₁ haux₂ a b c d hab hcd hb hd

end Ordered3Graph
end ThreeUniformDiaries
