import ThreeUniformDiaries.ActualFiniteEmbeddingMeets
import ThreeUniformDiaries.CoordinateTypeMeets

/-!
# Actual finite embedding induces the exact selected type-node meet

Unlike the earlier finite-encoder meet calculation, the hypotheses
here impose edge preservation only for actual source vertices < m,
and one/aux type agreement only for comparisons among them.

Both coordinate-tree meet formulas nevertheless remain literally
valid for every node used by the finite Aemb coding.
-/

namespace ThreeUniformDiaries
namespace EnumNode

private theorem min_strictMono_image
    (f : Nat → Nat) (hf : StrictMono f) (a b : Nat) :
    min (f a) (f b) = f (min a b) := by
  rcases le_total a b with hab | hba
  · simp [min_eq_left hab, min_eq_left (hf.monotone hab)]
  · simp [min_eq_right hba, min_eq_right (hf.monotone hba)]

/-- The exact meet level of two finite selected singleton type nodes
without a global zero-extension embedding premise. -/
theorem selectedOne_meetLevel_of_finite
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph H.toOrdered3Graph f m)
    (i j u v : Nat)
    (hiu : i ≤ u) (hjv : j ≤ v)
    (hu : u < m) (hv : v < m) :
    CoordNode.meetLevel
      (.one (f i) (H.oneType (f i) (f u)))
      (.one (f j) (H.oneType (f j) (f v))) =
      f (min (min i j) (A.toOrdered3Graph.oneMeetLevel u v)) := by
  have hc := hf.oneMeetLevel_eq u v hu hv
  rw [CoordNode.oneType_meetLevel_eq H
      (hf.strictMono.monotone hiu)
      (hf.strictMono.monotone hjv),
    hc,
    min_strictMono_image f hf.strictMono i j,
    min_strictMono_image f hf.strictMono
      (min i j) (A.toOrdered3Graph.oneMeetLevel u v)]

/-- The analogous exact auxiliary type-node meet for two genuine
source pairs lying inside the finite A. -/
theorem selectedAux_meetLevel_of_finite
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph H.toOrdered3Graph f m)
    (i j u₀ u₁ v₀ v₁ : Nat)
    (hiu : i ≤ u₀) (hu : u₀ < u₁) (hu₁ : u₁ < m)
    (hjv : j ≤ v₀) (hv : v₀ < v₁) (hv₁ : v₁ < m) :
    CoordNode.meetLevel
      (.aux (f i) (H.auxType (f i) (f u₀) (f u₁)))
      (.aux (f j) (H.auxType (f j) (f v₀) (f v₁))) =
      f (min (min i j)
        (A.toOrdered3Graph.auxMeetLevel u₀ u₁ v₀ v₁)) := by
  have hc := hf.auxMeetLevel_eq u₀ u₁ v₀ v₁ hu hv hu₁ hv₁
  rw [CoordNode.auxType_meetLevel_eq H
      (hf.strictMono.monotone hiu)
      (hf.strictMono.monotone hjv),
    hc,
    min_strictMono_image f hf.strictMono i j,
    min_strictMono_image f hf.strictMono
      (min i j) (A.toOrdered3Graph.auxMeetLevel u₀ u₁ v₀ v₁)]

end EnumNode
end ThreeUniformDiaries
