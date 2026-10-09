import ThreeUniformDiaries.TypeNodePrefix
import ThreeUniformDiaries.ExactTypeMeetLevels
import Mathlib.Data.Nat.Find

/-!
# Meets of finite type nodes at different cut levels

The finite converse Aemb uses singleton and auxiliary type nodes
belonging to different cuts of the same ambient enumeration.
Their common prefixes are characterised entirely by source type
agreement. The calculation of their greatest common prefix is the
algebraic ingredient behind E1/E2 meet-closure.
-/

namespace ThreeUniformDiaries
namespace EnumNode

/-- Two singleton-type nodes at potentially different levels agree
below a common smaller cut precisely when the vertices have the
same 1-type below that cut. -/
theorem oneType_crossCut_prefix_eq_iff
    {N l₀ l₁ k u v : Nat} (H : EnumNode N)
    (hk₀ : k ≤ l₀) (hk₁ : k ≤ l₁) :
    (H.oneType l₀ u).truncate k =
      (H.oneType l₁ v).truncate k ↔
        H.toOrdered3Graph.SameOneTypeBelow k u v := by
  rw [H.oneType_truncate (u := u) hk₀,
    H.oneType_truncate (u := v) hk₁]
  exact H.oneType_eq_iff_sameOneTypeBelow

/-- Auxiliary types over different cuts obey the analogous exact
common-prefix criterion. -/
theorem auxType_crossCut_prefix_eq_iff
    {N l₀ l₁ k u₀ u₁ v₀ v₁ : Nat} (H : EnumNode N)
    (hk₀ : k ≤ l₀) (hk₁ : k ≤ l₁) :
    (H.auxType l₀ u₀ u₁).truncate k =
      (H.auxType l₁ v₀ v₁).truncate k ↔
        H.toOrdered3Graph.SameAuxTypeBelow k u₀ u₁ v₀ v₁ := by
  rw [H.auxType_truncate (u := u₀) (v := u₁) hk₀,
    H.auxType_truncate (u := v₀) (v := v₁) hk₁]
  exact H.auxType_eq_iff_sameAuxTypeBelow

end EnumNode
end ThreeUniformDiaries
