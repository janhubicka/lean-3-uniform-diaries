import ThreeUniformDiaries.ExactMeetsFromTypes

/-!
# Exact meets require only finite source cut comparisons

The auxiliary Ramsey manuscript's finite converse starts with an
embedding of a FINITE enumerated hypergraph A, not an aux-respecting
embedding of its infinitely zero-extended graph.

The previous finite-encoder lemmas use an induced embedding on Nat
that globally preserves all aux types, a strictly stronger
hypothesis. Here we isolate the exact finite selected-cut condition.
Only type comparisons whose actual source vertices lie below the
finite bound m are needed to obtain exact capped meet preservation
for such vertices. There is no requirement about auxiliary types
involving artificial source vertices >= m.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph
namespace Embedding

variable {H G : Ordered3Graph Nat} (e : Embedding H G)

/-- Finite selected-cut type preservation: only comparisons among
the genuine first m source vertices are required. Both directions
are recorded for alignment with the manuscript definition. -/
structure FiniteSelectedTypeRespecting (m : Nat) : Prop where
  one :
    ∀ w u v : Nat, w ≤ u → w ≤ v → u < m → v < m →
      (H.SameOneTypeBelow w u v ↔
        G.SameOneTypeBelow (e w) (e u) (e v))
  aux :
    ∀ w u₀ u₁ v₀ v₁ : Nat,
      w ≤ u₀ → u₀ < u₁ → w ≤ v₀ → v₀ < v₁ →
      u₁ < m → v₁ < m →
      (H.SameAuxTypeBelow w u₀ u₁ v₀ v₁ ↔
        G.SameAuxTypeBelow (e w)
          (e u₀) (e u₁) (e v₀) (e v₁))

/-- Global aux-type preservation implies its genuinely finite
restriction, but the converse need not hold. -/
theorem AuxTypeRespecting.finiteSelected
    (haux : e.AuxTypeRespecting) (m : Nat) :
    e.FiniteSelectedTypeRespecting m := by
  constructor
  · intro w u v hwu hwv _ _
    exact haux.one w u v hwu hwv
  · intro w u₀ u₁ v₀ v₁ hwu hu hwv hv _ _
    exact haux.aux w u₀ u₁ v₀ v₁ hwu hu hwv hv

/-- Exact singleton meets for genuine finite vertices require only
their selected-cut comparison, not global aux-type preservation. -/
theorem finiteOneMeetLevel_eq
    {m : Nat} (hf : e.FiniteSelectedTypeRespecting m)
    (u v : Nat) (hu : u < m) (hv : v < m) :
    G.oneMeetLevel (e u) (e v) = e (H.oneMeetLevel u v) := by
  classical
  let w := H.oneMeetLevel u v
  have hbound : w ≤ min u v := H.oneMeetLevel_le_min u v
  have hwu : w ≤ u := hbound.trans (min_le_left _ _)
  have hwv : w ≤ v := hbound.trans (min_le_right _ _)
  have hagree : H.SameOneTypeBelow w u v := H.oneMeetLevel_agree u v
  have htarget : G.SameOneTypeBelow (e w) (e u) (e v) :=
    (hf.one w u v hwu hwv hu hv).mp hagree
  have htargetBound : e w ≤ min (e u) (e v) :=
    le_min (e.strictMono.monotone hwu) (e.strictMono.monotone hwv)
  have hlow : e w ≤ G.oneMeetLevel (e u) (e v) :=
    Nat.le_findGreatest htargetBound htarget
  have hupper : G.oneMeetLevel (e u) (e v) ≤ min (e u) (e v) :=
    G.oneMeetLevel_le_min (e u) (e v)
  by_cases hcap : w = min u v
  · have hmin : min (e u) (e v) = e (min u v) := by
      rcases le_total u v with huv | hvu
      · simp [min_eq_left huv,
          min_eq_left (e.strictMono.monotone huv)]
      · simp [min_eq_right hvu,
          min_eq_right (e.strictMono.monotone hvu)]
    have hhigh : G.oneMeetLevel (e u) (e v) ≤ e w := by
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
    have htargetFail :
        ¬ G.SameOneTypeBelow (e w + 1) (e u) (e v) :=
      oneType_failure_at_image_cut H G e e.strictMono
        (fun a b c hab hbc => e.edge_iff hab hbc)
        w u v (by omega) (by omega) hagree hfail
    have htop : G.oneMeetLevel (e u) (e v) < e w + 1 := by
      by_contra hn
      have hcut : e w + 1 ≤ G.oneMeetLevel (e u) (e v) :=
        Nat.le_of_not_gt hn
      have hall := G.oneMeetLevel_agree (e u) (e v)
      have hbad : G.SameOneTypeBelow (e w + 1) (e u) (e v) := by
        intro a b hab hb
        exact hall hab (lt_of_lt_of_le hb hcut)
      exact htargetFail hbad
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp htop) hlow

/-- Exact auxiliary meets for genuine ordered pairs require only
the finitely many comparisons on their actual source endpoints. -/
theorem finiteAuxMeetLevel_eq
    {m : Nat} (hf : e.FiniteSelectedTypeRespecting m)
    (u₀ u₁ v₀ v₁ : Nat) (hu : u₀ < u₁) (hv : v₀ < v₁)
    (hu₁ : u₁ < m) (hv₁ : v₁ < m) :
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
    (hf.aux w u₀ u₁ v₀ v₁ hwu hu hwv hv hu₁ hv₁).mp hagree
  have htargetBound : e w ≤ min (e u₀) (e v₀) :=
    le_min (e.strictMono.monotone hwu) (e.strictMono.monotone hwv)
  have hlow : e w ≤
      G.auxMeetLevel (e u₀) (e u₁) (e v₀) (e v₁) :=
    Nat.le_findGreatest htargetBound htarget
  have hupper :
      G.auxMeetLevel (e u₀) (e u₁) (e v₀) (e v₁) ≤
        min (e u₀) (e v₀) :=
    G.auxMeetLevel_le_min (e u₀) (e u₁) (e v₀) (e v₁)
  by_cases hcap : w = min u₀ v₀
  · have hmin : min (e u₀) (e v₀) = e (min u₀ v₀) := by
      rcases le_total u₀ v₀ with huv | hvu
      · simp [min_eq_left huv,
          min_eq_left (e.strictMono.monotone huv)]
      · simp [min_eq_right hvu,
          min_eq_right (e.strictMono.monotone hvu)]
    have hhigh : G.auxMeetLevel (e u₀) (e u₁)
        (e v₀) (e v₁) ≤ e w := by
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
    have htargetFail :
        ¬ G.SameAuxTypeBelow (e w + 1)
          (e u₀) (e u₁) (e v₀) (e v₁) :=
      auxType_failure_at_image_cut H G e e.strictMono
        (fun a b c hab hbc => e.edge_iff hab hbc)
        w u₀ u₁ v₀ v₁ (by omega) hu (by omega) hv
        hfail hagree
    have htop : G.auxMeetLevel (e u₀) (e u₁)
        (e v₀) (e v₁) < e w + 1 := by
      by_contra hn
      have hcut : e w + 1 ≤
          G.auxMeetLevel (e u₀) (e u₁) (e v₀) (e v₁) :=
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
