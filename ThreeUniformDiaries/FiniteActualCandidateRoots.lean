import ThreeUniformDiaries.FiniteActualCandidateMeetClosure
import ThreeUniformDiaries.PrunedTypeTrees

/-!
# Roots and levels of the finite E1/E2 candidates: genuine finite interface

The three prescribed coordinate pictures depend only on the finite
vertex map f, not on any induced/aux-type behaviour on source
vertices artificially placed after the last actual vertex m-1.

This file proves the root and selected-level conditions required
to apply generic finite strong completion under the genuine
FiniteAuxEmbedding hypothesis.
-/

namespace ThreeUniformDiaries
namespace EnumNode

/-- Only genuinely selected levels f(i), i<m, occur in E1. -/
theorem oneCandidate_levels_of_map
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat) (n : Nat) (hnm : n ≤ m)
    (hfix : ∀ k < n, f k = k)
    (x : CoordNode) (hx : finiteOneCandidate A H f n x) :
    ∃ i : Nat, i < m ∧ CoordNode.level x = f i := by
  rcases hx with ⟨k, B, hk, rfl⟩ |
      ⟨i, v, hni, hiv, hv, rfl⟩
  · exact ⟨k, lt_of_lt_of_le hk hnm, by
      simpa only [CoordNode.level] using (hfix k hk).symm⟩
  · exact ⟨i, lt_of_le_of_lt hiv hv, rfl⟩

/-- Only genuine selected levels occur in the E2^- auxiliary picture. -/
theorem auxCandidate_levels_of_map
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat) (n : Nat) (hnm : n ≤ m)
    (hfix : ∀ k < n, f k = k)
    (x : CoordNode) (hx : finiteAuxCandidate A H f n x) :
    ∃ i : Nat, i < m ∧ CoordNode.level x = f i := by
  rcases hx with ⟨k, B, hk, rfl⟩ |
      ⟨i, u₀, u₁, hni, hiu, hu, hum, rfl⟩
  · exact ⟨k, lt_of_lt_of_le hk hnm, by
      simpa only [CoordNode.level] using (hfix k hk).symm⟩
  · exact ⟨i, lt_trans (lt_of_le_of_lt hiu hu) hum, rfl⟩

private theorem oneRootZeroBelow {k : Nat} (B : OneNode k) :
    CoordNode.one 0 (OneNode.zero 0) ≤ .one k B := by
  refine ⟨Nat.zero_le _, ?_⟩
  change CoordNode.one 0 (B.truncate 0) =
    .one 0 (OneNode.zero 0)
  have heq : B.truncate 0 = OneNode.zero 0 := by
    apply OneNode.ext_pairs
    funext a b
    simp [OneNode.truncate, OneNode.zero]
  exact congrArg (CoordNode.one 0) heq

private theorem auxRootZeroBelow {k : Nat} (B : AuxNode k) :
    CoordNode.aux 0 (AuxNode.zero 0) ≤ .aux k B := by
  refine ⟨Nat.zero_le _, ?_⟩
  change CoordNode.aux 0 (B.truncate 0) =
    .aux 0 (AuxNode.zero 0)
  have heq : B.truncate 0 = AuxNode.zero 0 := by
    apply AuxNode.ext_bits
    funext a
    simp [AuxNode.truncate, AuxNode.zero]
  exact congrArg (CoordNode.aux 0) heq

/-- A first selected singleton root exists for an actual finite
type-respecting embedding, without any global zero-extension property. -/
theorem finiteOne_root_of_finite
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph H.toOrdered3Graph f m)
    (n : Nat) (hm : 0 < m)
    (hfix : ∀ k < n, f k = k) :
    ∃ r : CoordNode,
      CoordNode.level r = f 0 ∧
      ∀ x, finiteOneCandidate A H f n x → r ≤ x := by
  by_cases hz : n = 0
  · subst n
    let r := CoordNode.one (f 0) (H.oneType (f 0) (f 0))
    refine ⟨r, rfl, ?_⟩
    intro x hx
    rcases hx with ⟨k, B, hk, hxeq⟩ |
      ⟨i, v, hni, hiv, hvm, rfl⟩
    · omega
    · have hcut : f 0 ≤ f i :=
        hf.strictMono.monotone (Nat.zero_le i)
      refine ⟨hcut, ?_⟩
      change CoordNode.one (f 0)
          ((H.oneType (f i) (f v)).truncate (f 0)) =
        CoordNode.one (f 0) (H.oneType (f 0) (f 0))
      rw [H.oneType_truncate (u := f v) hcut]
      have hsource :
          A.toOrdered3Graph.SameOneTypeBelow 0 v 0 := by
        intro a b hab hb
        omega
      have htarget :=
        (hf.one 0 v 0 (Nat.zero_le v) (Nat.zero_le 0)
          hvm hm).mp hsource
      have htype :
          H.oneType (f 0) (f v) = H.oneType (f 0) (f 0) :=
        (H.oneType_eq_iff_sameOneTypeBelow).mpr htarget
      rw [htype]
  · have hn : 0 < n := by omega
    let r := CoordNode.one 0 (OneNode.zero 0)
    have h0 : f 0 = 0 := hfix 0 hn
    refine ⟨r, by rw [h0]; rfl, ?_⟩
    intro x hx
    rcases hx with ⟨k, B, hk, rfl⟩ |
      ⟨i, v, hni, hiv, hvm, rfl⟩
    · exact oneRootZeroBelow B
    · exact oneRootZeroBelow (H.oneType (f i) (f v))

/-- An auxiliary first selected root exists under genuinely finite
type agreement. The m=1,n=0 case has empty E2^- and any aux
node at f(0) is a valid root. -/
theorem finiteAux_root_of_finite
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph H.toOrdered3Graph f m)
    (n : Nat) (hm : 0 < m)
    (hfix : ∀ k < n, f k = k) :
    ∃ r : CoordNode,
      CoordNode.level r = f 0 ∧
      ∀ x, finiteAuxCandidate A H f n x → r ≤ x := by
  by_cases hz : n = 0
  · subst n
    by_cases hm2 : 1 < m
    · let r := CoordNode.aux (f 0)
        (H.auxType (f 0) (f 0) (f 1))
      refine ⟨r, rfl, ?_⟩
      intro x hx
      rcases hx with ⟨k, B, hk, hxeq⟩ |
        ⟨i, u₀, u₁, hni, hiu, hu, hum, rfl⟩
      · omega
      · have hcut : f 0 ≤ f i :=
          hf.strictMono.monotone (Nat.zero_le i)
        refine ⟨hcut, ?_⟩
        change CoordNode.aux (f 0)
            ((H.auxType (f i) (f u₀) (f u₁)).truncate (f 0)) =
          CoordNode.aux (f 0)
            (H.auxType (f 0) (f 0) (f 1))
        rw [H.auxType_truncate
          (u := f u₀) (v := f u₁) hcut]
        have hsource :
            A.toOrdered3Graph.SameAuxTypeBelow
              0 u₀ u₁ 0 1 := by
          intro a ha
          omega
        have htarget :=
          (hf.aux 0 u₀ u₁ 0 1 (Nat.zero_le u₀) hu
            (Nat.zero_le 0) Nat.zero_lt_one hum hm2).mp
            hsource
        have htype :
            H.auxType (f 0) (f u₀) (f u₁) =
              H.auxType (f 0) (f 0) (f 1) :=
          (H.auxType_eq_iff_sameAuxTypeBelow).mpr htarget
        rw [htype]
    · have hm1 : m = 1 := by omega
      subst m
      let r := CoordNode.aux (f 0) (AuxNode.zero (f 0))
      refine ⟨r, rfl, ?_⟩
      intro x hx
      rcases hx with ⟨k, B, hk, hxeq⟩ |
        ⟨i, u₀, u₁, hni, hiu, hu, hum, hxeq⟩
      · omega
      · omega
  · have hn : 0 < n := by omega
    let r := CoordNode.aux 0 (AuxNode.zero 0)
    have h0 : f 0 = 0 := hfix 0 hn
    refine ⟨r, by rw [h0]; rfl, ?_⟩
    intro x hx
    rcases hx with ⟨k, B, hk, rfl⟩ |
      ⟨i, u₀, u₁, hni, hiu, hu, hum, rfl⟩
    · exact auxRootZeroBelow B
    · exact auxRootZeroBelow (H.auxType (f i) (f u₀) (f u₁))

end EnumNode
end ThreeUniformDiaries
