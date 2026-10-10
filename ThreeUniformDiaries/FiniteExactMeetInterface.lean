import ThreeUniformDiaries.ActualFiniteEmbeddingMeets

/-!
# Equivalence of the finite selected-cut and exact-meet interfaces

The manuscript defines an aux-type-respecting embedding by preserving
the *exact capped* singleton and auxiliary meet levels. The finite
Aemb formalisation uses FiniteAuxEmbedding, whose fields compare
singleton/auxiliary type agreement at every selected source cut.

These are EQUIVALENT for actual finite source vertices. This module
proves the reverse direction, complementing the already checked
finite meet-preservation theorems, so no stronger hypothesis has been
silently substituted in the verified finite converse.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Below the cap min(u,v), agreement at cut w is equivalent to w
being at most the greatest agreement cut. -/
theorem sameOneTypeBelow_iff_le_oneMeetLevel
    (H : Ordered3Graph Nat) (w u v : Nat)
    (hw : w ≤ min u v) :
    H.SameOneTypeBelow w u v ↔ w ≤ H.oneMeetLevel u v := by
  classical
  constructor
  · intro h
    exact Nat.le_findGreatest hw h
  · intro hwmeet a b hab hb
    exact (H.oneMeetLevel_agree u v) hab
      (lt_of_lt_of_le hb hwmeet)

/-- The same equivalence holds for the capped auxiliary pair meet. -/
theorem sameAuxTypeBelow_iff_le_auxMeetLevel
    (H : Ordered3Graph Nat) (w u₀ u₁ v₀ v₁ : Nat)
    (hw : w ≤ min u₀ v₀) :
    H.SameAuxTypeBelow w u₀ u₁ v₀ v₁ ↔
      w ≤ H.auxMeetLevel u₀ u₁ v₀ v₁ := by
  classical
  constructor
  · intro h
    exact Nat.le_findGreatest hw h
  · intro hwmeet a ha
    exact (H.auxMeetLevel_agree u₀ u₁ v₀ v₁)
      (lt_of_lt_of_le ha hwmeet)

/-- A strict monotone map on Nat reflects the order as well as
preserving it. -/
private theorem strictMonoNat_le_iff
    {f : Nat → Nat} (hf : StrictMono f) (a b : Nat) :
    a ≤ b ↔ f a ≤ f b := by
  constructor
  · intro hab
    exact hf.monotone hab
  · intro h
    by_contra hn
    have hba : b < a := Nat.lt_of_not_ge hn
    have hstrict := hf hba
    omega

/-- The manuscript's genuine finite exact-meet formulation. -/
structure FiniteExactMeetEmbedding
    (H G : Ordered3Graph Nat) (f : Nat → Nat) (m : Nat) : Prop where
  strictMono : StrictMono f
  edge_iff :
    ∀ a b c : Nat, a < b → b < c → c < m →
      (H.edge a b c ↔ G.edge (f a) (f b) (f c))
  oneMeet :
    ∀ u v : Nat, u < m → v < m →
      G.oneMeetLevel (f u) (f v) = f (H.oneMeetLevel u v)
  auxMeet :
    ∀ u₀ u₁ v₀ v₁ : Nat,
      u₀ < u₁ → v₀ < v₁ → u₁ < m → v₁ < m →
        G.auxMeetLevel (f u₀) (f u₁) (f v₀) (f v₁) =
          f (H.auxMeetLevel u₀ u₁ v₀ v₁)

namespace FiniteExactMeetEmbedding

/-- Every finite exact-meet embedding preserves the selected-cut
type comparisons used in the finite canonical coding proof. -/
theorem toFiniteAuxEmbedding
    {H G : Ordered3Graph Nat} {f : Nat → Nat} {m : Nat}
    (h : FiniteExactMeetEmbedding H G f m) :
    FiniteAuxEmbedding H G f m := by
  refine ⟨h.strictMono, h.edge_iff, ?_, ?_⟩
  · intro w u v hwu hwv hu hv
    have hbound : w ≤ min u v := le_min hwu hwv
    have htarget :
        f w ≤ min (f u) (f v) :=
      le_min (h.strictMono.monotone hwu)
        (h.strictMono.monotone hwv)
    calc
      H.SameOneTypeBelow w u v ↔
          w ≤ H.oneMeetLevel u v :=
        H.sameOneTypeBelow_iff_le_oneMeetLevel w u v hbound
      _ ↔ f w ≤ f (H.oneMeetLevel u v) :=
        strictMonoNat_le_iff h.strictMono w (H.oneMeetLevel u v)
      _ ↔ G.SameOneTypeBelow (f w) (f u) (f v) := by
        rw [← h.oneMeet u v hu hv]
        exact (G.sameOneTypeBelow_iff_le_oneMeetLevel
          (f w) (f u) (f v) htarget).symm
  · intro w u₀ u₁ v₀ v₁ hwu hu hwv hv hu₁ hv₁
    have hbound : w ≤ min u₀ v₀ := le_min hwu hwv
    have htarget :
        f w ≤ min (f u₀) (f v₀) :=
      le_min (h.strictMono.monotone hwu)
        (h.strictMono.monotone hwv)
    calc
      H.SameAuxTypeBelow w u₀ u₁ v₀ v₁ ↔
          w ≤ H.auxMeetLevel u₀ u₁ v₀ v₁ :=
        H.sameAuxTypeBelow_iff_le_auxMeetLevel
          w u₀ u₁ v₀ v₁ hbound
      _ ↔ f w ≤ f (H.auxMeetLevel u₀ u₁ v₀ v₁) :=
        strictMonoNat_le_iff h.strictMono w
          (H.auxMeetLevel u₀ u₁ v₀ v₁)
      _ ↔ G.SameAuxTypeBelow (f w)
          (f u₀) (f u₁) (f v₀) (f v₁) := by
        rw [← h.auxMeet u₀ u₁ v₀ v₁ hu hv hu₁ hv₁]
        exact (G.sameAuxTypeBelow_iff_le_auxMeetLevel
          (f w) (f u₀) (f u₁) (f v₀) (f v₁)
          htarget).symm

end FiniteExactMeetEmbedding

namespace FiniteAuxEmbedding

/-- Conversely, finite selected-cut agreement implies exact
preservation of both capped meets. -/
theorem toFiniteExactMeetEmbedding
    {H G : Ordered3Graph Nat} {f : Nat → Nat} {m : Nat}
    (h : FiniteAuxEmbedding H G f m) :
    FiniteExactMeetEmbedding H G f m := by
  refine ⟨h.strictMono, h.edge_iff, ?_, ?_⟩
  · intro u v hu hv
    exact h.oneMeetLevel_eq u v hu hv
  · intro u₀ u₁ v₀ v₁ hu hv hu₁ hv₁
    exact h.auxMeetLevel_eq u₀ u₁ v₀ v₁ hu hv hu₁ hv₁

end FiniteAuxEmbedding

/-- The interface used by the finite Aemb Lean proof is genuinely
equivalent to the manuscript's definition restricted to actual
source vertices, including all skipped target positions. -/
theorem finiteAuxEmbedding_iff_exactMeetEmbedding
    (H G : Ordered3Graph Nat) (f : Nat → Nat) (m : Nat) :
    FiniteAuxEmbedding H G f m ↔
      FiniteExactMeetEmbedding H G f m := by
  constructor
  · exact FiniteAuxEmbedding.toFiniteExactMeetEmbedding
  · exact FiniteExactMeetEmbedding.toFiniteAuxEmbedding

end Ordered3Graph
end ThreeUniformDiaries
