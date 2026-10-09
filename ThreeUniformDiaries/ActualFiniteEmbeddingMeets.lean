import ThreeUniformDiaries.ExactMeetsFromTypes

/-!
# Exact meets for genuine finite embeddings into an arbitrary target

The source of manuscript Lemma Aemb has only m actual vertices.
Unlike an embedding of its infinitely zero-extended graph, a finite
embedding need preserve edges and aux-type agreements ONLY among
vertices below m. There is no requirement to preserve any edge or
type involving artificially added vertices >= m.

This module proves that the finite requirements suffice to preserve
literal capped singleton and auxiliary meet levels between actual
source vertices, despite arbitrarily many omitted target vertices.

We use a strictly increasing function Nat -> Nat to represent the
finite vertex map, but impose every logical requirement only below m.
Any strictly increasing map on Fin m may be monotonically extended
without imposing further edge conditions.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- A finite induced embedding plus the selected-cut type agreement
required in the finite Aemb lemma. In particular, the target G may
be any enumerated 3-hypergraph, not necessarily a zero extension. -/
structure FiniteAuxEmbedding
    (H G : Ordered3Graph Nat) (f : Nat → Nat) (m : Nat) : Prop where
  strictMono : StrictMono f
  edge_iff :
    ∀ a b c : Nat, a < b → b < c → c < m →
      (H.edge a b c ↔ G.edge (f a) (f b) (f c))
  one :
    ∀ w u v : Nat, w ≤ u → w ≤ v → u < m → v < m →
      (H.SameOneTypeBelow w u v ↔
        G.SameOneTypeBelow (f w) (f u) (f v))
  aux :
    ∀ w u₀ u₁ v₀ v₁ : Nat,
      w ≤ u₀ → u₀ < u₁ → w ≤ v₀ → v₀ < v₁ →
      u₁ < m → v₁ < m →
      (H.SameAuxTypeBelow w u₀ u₁ v₀ v₁ ↔
        G.SameAuxTypeBelow (f w)
          (f u₀) (f u₁) (f v₀) (f v₁))

namespace FiniteAuxEmbedding

variable {H G : Ordered3Graph Nat} {f : Nat → Nat} {m : Nat}
/-- Exact singleton meets on actual finite source vertices, proved
using the first-disagreement witness at the source meet. -/
theorem oneMeetLevel_eq
    (h : FiniteAuxEmbedding H G f m)
    (u v : Nat) (hu : u < m) (hv : v < m) :
    G.oneMeetLevel (f u) (f v) = f (H.oneMeetLevel u v) := by
  classical
  let w := H.oneMeetLevel u v
  have hbound : w ≤ min u v := H.oneMeetLevel_le_min u v
  have hwu : w ≤ u := hbound.trans (min_le_left _ _)
  have hwv : w ≤ v := hbound.trans (min_le_right _ _)
  have hagree : H.SameOneTypeBelow w u v := H.oneMeetLevel_agree u v
  have htarget : G.SameOneTypeBelow (f w) (f u) (f v) :=
    (h.one w u v hwu hwv hu hv).mp hagree
  have htargetBound : f w ≤ min (f u) (f v) :=
    le_min (h.strictMono.monotone hwu) (h.strictMono.monotone hwv)
  have hlow : f w ≤ G.oneMeetLevel (f u) (f v) :=
    Nat.le_findGreatest htargetBound htarget
  have hupper : G.oneMeetLevel (f u) (f v) ≤ min (f u) (f v) :=
    G.oneMeetLevel_le_min (f u) (f v)
  by_cases hcap : w = min u v
  · have hmin : min (f u) (f v) = f (min u v) := by
      rcases le_total u v with huv | hvu
      · simp [min_eq_left huv,
          min_eq_left (h.strictMono.monotone huv)]
      · simp [min_eq_right hvu,
          min_eq_right (h.strictMono.monotone hvu)]
    have hhigh : G.oneMeetLevel (f u) (f v) ≤ f w := by
      rw [hcap, ← hmin]
      exact hupper
    exact Nat.le_antisymm hhigh hlow
  · have hwlt : w < min u v := by omega
    have hfail : ¬ H.SameOneTypeBelow (w + 1) u v := by
      intro hnext
      have hwplus : w + 1 ≤ min u v := by omega
      have hh : w + 1 ≤ H.oneMeetLevel u v :=
        Nat.le_findGreatest hwplus hnext
      omega
    have hnew : ¬ ∀ a : Nat, a < w →
        (H.edge a w u ↔ H.edge a w v) := by
      intro hnext
      exact hfail
        ((H.sameOneTypeBelow_succ_iff w u v).mpr
          ⟨hagree, hnext⟩)
    push_neg at hnew
    rcases hnew with ⟨a, haw, hdiff⟩
    have htargetFail :
        ¬ G.SameOneTypeBelow (f w + 1) (f u) (f v) := by
      intro hnext
      have heq := hnext (h.strictMono haw)
        (by omega : f w < f w + 1)
      have hleft := h.edge_iff a w u haw (by omega) hu
      have hright := h.edge_iff a w v haw (by omega) hv
      have hbit := hleft.trans (heq.trans hright.symm)
      rcases hdiff with ha | ha
      · exact ha.2 (hbit.mp ha.1)
      · exact ha.1 (hbit.mpr ha.2)
    have htop : G.oneMeetLevel (f u) (f v) < f w + 1 := by
      by_contra hn
      have hcut : f w + 1 ≤ G.oneMeetLevel (f u) (f v) :=
        Nat.le_of_not_gt hn
      have hall := G.oneMeetLevel_agree (f u) (f v)
      have hbad : G.SameOneTypeBelow (f w + 1) (f u) (f v) := by
        intro a b hab hb
        exact hall hab (lt_of_lt_of_le hb hcut)
      exact htargetFail hbad
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp htop) hlow

/-- Exact auxiliary meets on actual ordered pairs, requiring edge
preservation only on triples lying wholly inside the finite source. -/
theorem auxMeetLevel_eq
    (h : FiniteAuxEmbedding H G f m)
    (u₀ u₁ v₀ v₁ : Nat)
    (hu : u₀ < u₁) (hv : v₀ < v₁)
    (hu₁ : u₁ < m) (hv₁ : v₁ < m) :
    G.auxMeetLevel (f u₀) (f u₁) (f v₀) (f v₁) =
      f (H.auxMeetLevel u₀ u₁ v₀ v₁) := by
  classical
  let w := H.auxMeetLevel u₀ u₁ v₀ v₁
  have hbound : w ≤ min u₀ v₀ :=
    H.auxMeetLevel_le_min u₀ u₁ v₀ v₁
  have hwu : w ≤ u₀ := hbound.trans (min_le_left _ _)
  have hwv : w ≤ v₀ := hbound.trans (min_le_right _ _)
  have hagree : H.SameAuxTypeBelow w u₀ u₁ v₀ v₁ :=
    H.auxMeetLevel_agree u₀ u₁ v₀ v₁
  have htarget : G.SameAuxTypeBelow (f w)
      (f u₀) (f u₁) (f v₀) (f v₁) :=
    (h.aux w u₀ u₁ v₀ v₁ hwu hu hwv hv hu₁ hv₁).mp hagree
  have htargetBound : f w ≤ min (f u₀) (f v₀) :=
    le_min (h.strictMono.monotone hwu) (h.strictMono.monotone hwv)
  have hlow : f w ≤
      G.auxMeetLevel (f u₀) (f u₁) (f v₀) (f v₁) :=
    Nat.le_findGreatest htargetBound htarget
  have hupper :
      G.auxMeetLevel (f u₀) (f u₁) (f v₀) (f v₁) ≤
        min (f u₀) (f v₀) :=
    G.auxMeetLevel_le_min (f u₀) (f u₁) (f v₀) (f v₁)
  by_cases hcap : w = min u₀ v₀
  · have hmin : min (f u₀) (f v₀) = f (min u₀ v₀) := by
      rcases le_total u₀ v₀ with huv | hvu
      · simp [min_eq_left huv,
          min_eq_left (h.strictMono.monotone huv)]
      · simp [min_eq_right hvu,
          min_eq_right (h.strictMono.monotone hvu)]
    have hhigh : G.auxMeetLevel (f u₀) (f u₁)
        (f v₀) (f v₁) ≤ f w := by
      rw [hcap, ← hmin]
      exact hupper
    exact Nat.le_antisymm hhigh hlow
  · have hwlt : w < min u₀ v₀ := by omega
    have hfail :
        ¬ H.SameAuxTypeBelow (w + 1) u₀ u₁ v₀ v₁ := by
      intro hnext
      have hwplus : w + 1 ≤ min u₀ v₀ := by omega
      have hh : w + 1 ≤ H.auxMeetLevel u₀ u₁ v₀ v₁ :=
        Nat.le_findGreatest hwplus hnext
      omega
    have hdiff :
        ¬ (H.edge w u₀ u₁ ↔ H.edge w v₀ v₁) := by
      intro heq
      exact hfail
        ((H.sameAuxTypeBelow_succ_iff w u₀ u₁ v₀ v₁).mpr
          ⟨hagree, heq⟩)
    have htargetFail :
        ¬ G.SameAuxTypeBelow (f w + 1)
          (f u₀) (f u₁) (f v₀) (f v₁) := by
      intro hnext
      have heq := hnext (by omega : f w < f w + 1)
      have hleft := h.edge_iff w u₀ u₁ (by omega) hu hu₁
      have hright := h.edge_iff w v₀ v₁ (by omega) hv hv₁
      exact hdiff (hleft.trans (heq.trans hright.symm))
    have htop : G.auxMeetLevel (f u₀) (f u₁)
        (f v₀) (f v₁) < f w + 1 := by
      by_contra hn
      have hcut : f w + 1 ≤
          G.auxMeetLevel (f u₀) (f u₁) (f v₀) (f v₁) :=
        Nat.le_of_not_gt hn
      have hall := G.auxMeetLevel_agree
        (f u₀) (f u₁) (f v₀) (f v₁)
      have hbad :
          G.SameAuxTypeBelow (f w + 1)
            (f u₀) (f u₁) (f v₀) (f v₁) := by
        intro a ha
        exact hall (lt_of_lt_of_le ha hcut)
      exact htargetFail hbad
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp htop) hlow

end FiniteAuxEmbedding
end Ordered3Graph
end ThreeUniformDiaries
