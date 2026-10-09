import ThreeUniformDiaries.ExactTypeMeetLevels
import ThreeUniformDiaries.AuxTypes

/-!
# Literal meet preservation from type-agreement preservation

The concrete inherited-gap lemma proves that omitted target vertices give
zero auxiliary tests for the *global* source embedding.  On a canonical
branch, however, vertices belonging to the global image but not to that
branch can have nonzero auxiliary tests.  They are controlled by the
source K_I type agreement, not by a zero condition.

This module proves literal meet preservation from the already appropriate
notion of aux-type-respecting embedding: preserving and reflecting type
agreement at selected cuts.  No zero hypothesis about omitted branch
vertices is needed.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph
namespace Embedding

variable {H G : Ordered3Graph Nat} (e : Embedding H G)

/-- Preservation of singleton types at corresponding cuts implies
equality of the actual capped singleton meet levels. -/
theorem oneMeetLevel_eq_of_auxTypeRespecting
    (hf : e.AuxTypeRespecting) (u v : Nat) :
    G.oneMeetLevel (e u) (e v) = e (H.oneMeetLevel u v) := by
  apply Ordered3Graph.oneMeetLevel_preserved H G e e.strictMono
    (fun a b c hab hbc => e.edge_iff hab hbc)
  intro w a b hwa hwb hs x y hxy hyw _
  exact (hf.one w a b hwa hwb).mp hs hxy hyw

/-- Preservation of auxiliary type agreements implies equality of
the literal capped auxiliary meet levels. This remains true when omitted
branch vertices are selected in a larger ambient embedding. -/
theorem auxMeetLevel_eq_of_auxTypeRespecting
    (hf : e.AuxTypeRespecting)
    (u₀ u₁ v₀ v₁ : Nat) (hu : u₀ < u₁) (hv : v₀ < v₁) :
    G.auxMeetLevel (e u₀) (e u₁) (e v₀) (e v₁) =
      e (H.auxMeetLevel u₀ u₁ v₀ v₁) := by
  classical
  let w := H.auxMeetLevel u₀ u₁ v₀ v₁
  have hbound : w ≤ min u₀ v₀ :=
    H.auxMeetLevel_le_min u₀ u₁ v₀ v₁
  have hwu : w ≤ u₀ := hbound.trans (min_le_left _ _)
  have hwv : w ≤ v₀ := hbound.trans (min_le_right _ _)
  have hagree : H.SameAuxTypeBelow w u₀ u₁ v₀ v₁ :=
    H.auxMeetLevel_agree u₀ u₁ v₀ v₁
  have htarget : G.SameAuxTypeBelow (e w)
      (e u₀) (e u₁) (e v₀) (e v₁) :=
    (hf.aux w u₀ u₁ v₀ v₁ hwu hu hwv hv).mp hagree
  have htargetBound : e w ≤ min (e u₀) (e v₀) :=
    le_min (e.strictMono.monotone hwu) (e.strictMono.monotone hwv)
  have hlow : e w ≤ G.auxMeetLevel (e u₀) (e u₁) (e v₀) (e v₁) :=
    Nat.le_findGreatest htargetBound htarget
  have hupper : G.auxMeetLevel (e u₀) (e u₁) (e v₀) (e v₁) ≤
      min (e u₀) (e v₀) :=
    G.auxMeetLevel_le_min (e u₀) (e u₁) (e v₀) (e v₁)
  by_cases hcap : w = min u₀ v₀
  · have hmin : min (e u₀) (e v₀) = e (min u₀ v₀) := by
      rcases le_total u₀ v₀ with huv | hvu
      · simp [min_eq_left huv, min_eq_left (e.strictMono.monotone huv)]
      · simp [min_eq_right hvu, min_eq_right (e.strictMono.monotone hvu)]
    have hhigh : G.auxMeetLevel (e u₀) (e u₁) (e v₀) (e v₁) ≤ e w := by
      rw [hcap, ← hmin]
      exact hupper
    exact Nat.le_antisymm hhigh hlow
  · have hwlt : w < min u₀ v₀ := by omega
    have hfail : ¬ H.SameAuxTypeBelow (w + 1) u₀ u₁ v₀ v₁ := by
      intro hnext
      have hwplus : w + 1 ≤ min u₀ v₀ := by omega
      have hh : w + 1 ≤ H.auxMeetLevel u₀ u₁ v₀ v₁ :=
        Nat.le_findGreatest hwplus hnext
      omega
    have htargetFail :
        ¬ G.SameAuxTypeBelow (e w + 1) (e u₀) (e u₁)
          (e v₀) (e v₁) :=
      auxType_failure_at_image_cut H G e e.strictMono
        (fun a b c hab hbc => e.edge_iff hab hbc)
        w u₀ u₁ v₀ v₁ (by omega) hu (by omega) hv hfail hagree
    have htop :
        G.auxMeetLevel (e u₀) (e u₁) (e v₀) (e v₁) < e w + 1 := by
      by_contra hn
      have hcut :
          e w + 1 ≤ G.auxMeetLevel (e u₀) (e u₁) (e v₀) (e v₁) :=
        Nat.le_of_not_gt hn
      have hall := G.auxMeetLevel_agree
        (e u₀) (e u₁) (e v₀) (e v₁)
      have hbad :
          G.SameAuxTypeBelow (e w + 1)
            (e u₀) (e u₁) (e v₀) (e v₁) := by
        intro a ha
        exact hall (lt_of_lt_of_le ha hcut)
      exact htargetFail hbad
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp htop) hlow

end Embedding
end Ordered3Graph
end ThreeUniformDiaries
