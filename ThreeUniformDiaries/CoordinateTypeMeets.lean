import ThreeUniformDiaries.MixedTypeMeetLevels
import ThreeUniformDiaries.CoordinateTree

/-!
# Concrete meets in the three-coordinate type tree

For singleton and auxiliary type nodes at different cuts, the
coordinate-tree meet level is the greatest common type prefix.
This connects the finite type calculations to the exact tree meet
used in the strong-subtree completion argument in Lemma Aemb.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The coordinate-tree meet of singleton type nodes has the exact
numerical cut formula, even when the two cuts differ. -/
theorem oneType_meetLevel_eq
    {N l₀ l₁ u v : Nat} (H : EnumNode N)
    (hlu : l₀ ≤ u) (hlv : l₁ ≤ v) :
    meetLevel
      (.one l₀ (H.oneType l₀ u))
      (.one l₁ (H.oneType l₁ v)) =
      min (min l₀ l₁) (H.toOrdered3Graph.oneMeetLevel u v) := by
  classical
  have h : meetLevel
      (.one l₀ (H.oneType l₀ u))
      (.one l₁ (H.oneType l₁ v)) =
      H.oneTypeCrossCutMeetLevel l₀ l₁ u v := by
    unfold meetLevel CommonAt EnumNode.oneTypeCrossCutMeetLevel
    simp [level, truncate]
  exact h.trans (H.oneType_greatest_common_prefix hlu hlv)

/-- The analogous precise formula for the auxiliary-type coordinate. -/
theorem auxType_meetLevel_eq
    {N l₀ l₁ u₀ u₁ v₀ v₁ : Nat} (H : EnumNode N)
    (hlu : l₀ ≤ u₀) (hlv : l₁ ≤ v₀) :
    meetLevel
      (.aux l₀ (H.auxType l₀ u₀ u₁))
      (.aux l₁ (H.auxType l₁ v₀ v₁)) =
      min (min l₀ l₁)
        (H.toOrdered3Graph.auxMeetLevel u₀ u₁ v₀ v₁) := by
  classical
  have h : meetLevel
      (.aux l₀ (H.auxType l₀ u₀ u₁))
      (.aux l₁ (H.auxType l₁ v₀ v₁)) =
      H.auxTypeCrossCutMeetLevel l₀ l₁ u₀ u₁ v₀ v₁ := by
    unfold meetLevel CommonAt EnumNode.auxTypeCrossCutMeetLevel
    simp [level, truncate]
  exact h.trans (H.auxType_greatest_common_prefix hlu hlv)

end CoordNode
end ThreeUniformDiaries
