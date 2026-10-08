import ThreeUniformDiaries.AgreementSuccessors

/-!
# Transferring type agreements across an induced embedding

The main embedding lemma requires comparisons over the entire target
interval below f(w), not only over the image of source vertices.
This file isolates the exact splitting of those tests into selected
vertices (handled by induced edge reflection and source agreement)
and globally omitted vertices (handled by gap inheritance).

It also proves that an edge witnessing a source type disagreement
at level w survives as a target disagreement at level f(w).
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

private theorem preimage_lt_of_strictMono
    {f : Nat → Nat} (hf : StrictMono f)
    {a b : Nat} (h : f a < f b) : a < b := by
  by_contra hn
  have hba : b ≤ a := Nat.le_of_not_gt hn
  exact (not_lt_of_ge (hf.monotone hba)) h

/-- The exact selected/omitted decomposition for singleton type
agreement below the image of a source cut. -/
theorem oneTypeAgreement_transfer
    (K G : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (hedge : ∀ a b c : Nat, a < b → b < c →
      (K.edge a b c ↔ G.edge (f a) (f b) (f c)))
    (w u v : Nat) (hwu : w ≤ u) (hwv : w ≤ v)
    (hsource : K.SameOneTypeBelow w u v)
    (hgap : ∀ x y : Nat, x < y → y < f w →
      ((¬ ∃ a, f a = x) ∨ (¬ ∃ b, f b = y)) →
      (G.edge x y (f u) ↔ G.edge x y (f v))) :
    G.SameOneTypeBelow (f w) (f u) (f v) := by
  intro x y hxy hyw
  classical
  by_cases hx : ∃ a, f a = x
  · by_cases hy : ∃ b, f b = y
    · rcases hx with ⟨a, rfl⟩
      rcases hy with ⟨b, rfl⟩
      have hab : a < b := preimage_lt_of_strictMono hf hxy
      have hbw : b < w := preimage_lt_of_strictMono hf hyw
      have hbu : b < u := lt_of_lt_of_le hbw hwu
      have hbv : b < v := lt_of_lt_of_le hbw hwv
      calc
        G.edge (f a) (f b) (f u) ↔ K.edge a b u :=
          (hedge a b u hab hbu).symm
        _ ↔ K.edge a b v := hsource hab hbw
        _ ↔ G.edge (f a) (f b) (f v) :=
          hedge a b v hab hbv
    · exact hgap x y hxy hyw (Or.inr hy)
  · exact hgap x y hxy hyw (Or.inl hx)

/-- For auxiliary types the omitted test vertex is required to
give a non-edge with both selected pairs. -/
theorem auxTypeAgreement_transfer
    (K G : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (hedge : ∀ a b c : Nat, a < b → b < c →
      (K.edge a b c ↔ G.edge (f a) (f b) (f c)))
    (w u₀ u₁ v₀ v₁ : Nat)
    (hwu : w ≤ u₀) (hu : u₀ < u₁)
    (hwv : w ≤ v₀) (hv : v₀ < v₁)
    (hsource : K.SameAuxTypeBelow w u₀ u₁ v₀ v₁)
    (hzero : ∀ x : Nat, x < f w → (¬ ∃ a, f a = x) →
      ¬ G.edge x (f u₀) (f u₁) ∧
      ¬ G.edge x (f v₀) (f v₁)) :
    G.SameAuxTypeBelow (f w) (f u₀) (f u₁) (f v₀) (f v₁) := by
  intro x hxw
  classical
  by_cases hx : ∃ a, f a = x
  · rcases hx with ⟨a, rfl⟩
    have haw : a < w := preimage_lt_of_strictMono hf hxw
    have hau : a < u₀ := lt_of_lt_of_le haw hwu
    have hav : a < v₀ := lt_of_lt_of_le haw hwv
    calc
      G.edge (f a) (f u₀) (f u₁) ↔ K.edge a u₀ u₁ :=
        (hedge a u₀ u₁ hau hu).symm
      _ ↔ K.edge a v₀ v₁ := hsource haw
      _ ↔ G.edge (f a) (f v₀) (f v₁) :=
        hedge a v₀ v₁ hav hv
  · rcases hzero x hxw hx with ⟨hleft, hright⟩
    exact iff_of_false hleft hright

/-- A singleton-type first-difference edge at source level w is
preserved at target level f(w), including any skipped target levels. -/
theorem oneType_failure_at_image_cut
    (K G : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (hedge : ∀ a b c : Nat, a < b → b < c →
      (K.edge a b c ↔ G.edge (f a) (f b) (f c)))
    (w u v : Nat) (hwu : w < u) (hwv : w < v)
    (hsource : K.SameOneTypeBelow w u v)
    (hfail : ¬ K.SameOneTypeBelow (w + 1) u v) :
    ¬ G.SameOneTypeBelow (f w + 1) (f u) (f v) := by
  intro htarget
  have hnew : ¬ ∀ a : Nat, a < w →
      (K.edge a w u ↔ K.edge a w v) := by
    intro hnext
    exact hfail ((K.sameOneTypeBelow_succ_iff w u v).mpr ⟨hsource,hnext⟩)
  push_neg at hnew
  rcases hnew with ⟨a, haw, hdiff⟩
  have hau : w < u := hwu
  have hav : w < v := hwv
  have htargetBit := htarget (hf haw) (by omega :
      f w < f w + 1)
  have hleft := hedge a w u haw hau
  have hright := hedge a w v haw hav
  have hEq := hleft.trans (htargetBit.trans hright.symm)
  rcases hdiff with h | h
  · exact h.2 (hEq.mp h.1)
  · exact h.1 (hEq.mpr h.2)

/-- A first auxiliary-type disagreement at w also survives at the
corresponding selected target vertex f(w). -/
theorem auxType_failure_at_image_cut
    (K G : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (hedge : ∀ a b c : Nat, a < b → b < c →
      (K.edge a b c ↔ G.edge (f a) (f b) (f c)))
    (w u₀ u₁ v₀ v₁ : Nat)
    (hwu : w < u₀) (hu : u₀ < u₁)
    (hwv : w < v₀) (hv : v₀ < v₁)
    (hfail : ¬ K.SameAuxTypeBelow (w + 1) u₀ u₁ v₀ v₁)
    (hsource : K.SameAuxTypeBelow w u₀ u₁ v₀ v₁) :
    ¬ G.SameAuxTypeBelow (f w + 1) (f u₀) (f u₁)
      (f v₀) (f v₁) := by
  intro htarget
  have hdiff : ¬ (K.edge w u₀ u₁ ↔ K.edge w v₀ v₁) := by
    intro heq
    exact hfail ((K.sameAuxTypeBelow_succ_iff w u₀ u₁ v₀ v₁).mpr ⟨hsource,heq⟩)
  have htargetBit := htarget (by omega : f w < f w + 1)
  have hleft := hedge w u₀ u₁ hwu hu
  have hright := hedge w v₀ v₁ hwv hv
  exact hdiff (hleft.trans (htargetBit.trans hright.symm))

end Ordered3Graph
end ThreeUniformDiaries
