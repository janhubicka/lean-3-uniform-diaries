import ThreeUniformDiaries.CoordinateTypeMeets
import ThreeUniformDiaries.ExactMeetsFromTypes

/-!
# Selected meet levels in the finite strong-tree encoding

In Lemma Aemb, a type node associated with a source cut i is
represented in the target at cut e(i). The two formulas below show
that the *tree meet level* of any two selected singleton-type or
auxiliary-type nodes is another selected image level e(k), where
k is the minimum of both source cuts and the source type meet.

This proves the numeric part of E1/E2 meet closure. It does not
yet assert membership of the meet node in the selected sets.
-/

namespace ThreeUniformDiaries
namespace EnumNode

private theorem min_map_of_monotone
    (f : Nat → Nat) (hf : Monotone f) (a b : Nat) :
    min (f a) (f b) = f (min a b) := by
  rcases le_total a b with hab | hba
  · simp [min_eq_left hab, min_eq_left (hf hab)]
  · simp [min_eq_right hba, min_eq_right (hf hba)]

/-- The meet level of two selected singleton-type nodes is a selected
image level. Source and target are connected by one aux-type-respecting
induced embedding e. -/
theorem selectedOne_meetLevel
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (e : Ordered3Graph.Embedding A.toOrdered3Graph H.toOrdered3Graph)
    (haux : e.AuxTypeRespecting)
    (i j u v : Nat) (hiu : i ≤ u) (hjv : j ≤ v) :
    CoordNode.meetLevel
      (.one (e i) (H.oneType (e i) (e u)))
      (.one (e j) (H.oneType (e j) (e v))) =
      e (min (min i j) (A.toOrdered3Graph.oneMeetLevel u v)) := by
  have hc : H.toOrdered3Graph.oneMeetLevel (e u) (e v) =
      e (A.toOrdered3Graph.oneMeetLevel u v) :=
    e.oneMeetLevel_eq_of_auxTypeRespecting haux u v
  rw [CoordNode.oneType_meetLevel_eq H
      (e.strictMono.monotone hiu) (e.strictMono.monotone hjv),
    hc,
    min_map_of_monotone e e.strictMono.monotone i j,
    min_map_of_monotone e e.strictMono.monotone
      (min i j) (A.toOrdered3Graph.oneMeetLevel u v)]

/-- The analogous selected-level formula for auxiliary type nodes.
The original pair endpoints may occur at different cuts. -/
theorem selectedAux_meetLevel
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (e : Ordered3Graph.Embedding A.toOrdered3Graph H.toOrdered3Graph)
    (haux : e.AuxTypeRespecting)
    (i j u₀ u₁ v₀ v₁ : Nat)
    (hiu : i ≤ u₀) (hu : u₀ < u₁)
    (hjv : j ≤ v₀) (hv : v₀ < v₁) :
    CoordNode.meetLevel
      (.aux (e i) (H.auxType (e i) (e u₀) (e u₁)))
      (.aux (e j) (H.auxType (e j) (e v₀) (e v₁))) =
      e (min (min i j)
        (A.toOrdered3Graph.auxMeetLevel u₀ u₁ v₀ v₁)) := by
  have hc : H.toOrdered3Graph.auxMeetLevel
      (e u₀) (e u₁) (e v₀) (e v₁) =
        e (A.toOrdered3Graph.auxMeetLevel u₀ u₁ v₀ v₁) :=
    e.auxMeetLevel_eq_of_auxTypeRespecting haux
      u₀ u₁ v₀ v₁ hu hv
  rw [CoordNode.auxType_meetLevel_eq H
      (e.strictMono.monotone hiu) (e.strictMono.monotone hjv),
    hc,
    min_map_of_monotone e e.strictMono.monotone i j,
    min_map_of_monotone e e.strictMono.monotone
      (min i j) (A.toOrdered3Graph.auxMeetLevel u₀ u₁ v₀ v₁)]

end EnumNode
end ThreeUniformDiaries
