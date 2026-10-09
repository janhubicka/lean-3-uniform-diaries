import ThreeUniformDiaries.MixedTypeNodeMeets
import ThreeUniformDiaries.ExactTypeMeetLevels
import Mathlib.Data.Nat.Find

/-!
# Formula for meets of finite singleton and auxiliary type nodes

For two type nodes cut off at l0 and l1, their last common
prefix is at the minimum of the two cut levels and the original
type-meet level. This formula, rather than an informal appeal to
meet preservation, supports the finite Aemb meet-closure argument.
-/

namespace ThreeUniformDiaries
namespace EnumNode

/-- Two singleton-type prefixes agree below k, provided k is below
both displayed levels, exactly when k is no later than the capped
singleton meet of their type vertices. -/
theorem oneType_crossCut_eq_iff_le_meet
    {N l₀ l₁ u v k : Nat} (H : EnumNode N)
    (hlu : l₀ ≤ u) (hlv : l₁ ≤ v)
    (hk : k ≤ min l₀ l₁) :
    (H.oneType l₀ u).truncate k =
        (H.oneType l₁ v).truncate k ↔
      k ≤ H.toOrdered3Graph.oneMeetLevel u v := by
  classical
  have hk₀ : k ≤ l₀ := hk.trans (min_le_left _ _)
  have hk₁ : k ≤ l₁ := hk.trans (min_le_right _ _)
  constructor
  · intro heq
    have hs : H.toOrdered3Graph.SameOneTypeBelow k u v :=
      (H.oneType_crossCut_prefix_eq_iff hk₀ hk₁).mp heq
    have hkbound : k ≤ min u v := le_min (hk₀.trans hlu) (hk₁.trans hlv)
    exact Nat.le_findGreatest hkbound hs
  · intro hkmeet
    apply (H.oneType_crossCut_prefix_eq_iff hk₀ hk₁).mpr
    have hs := H.toOrdered3Graph.oneMeetLevel_agree u v
    intro a b hab hb
    exact hs hab (lt_of_lt_of_le hb hkmeet)

/-- The same criterion for two auxiliary types of ordered pairs. -/
theorem auxType_crossCut_eq_iff_le_meet
    {N l₀ l₁ u₀ u₁ v₀ v₁ k : Nat} (H : EnumNode N)
    (hlu : l₀ ≤ u₀) (hlv : l₁ ≤ v₀)
    (hk : k ≤ min l₀ l₁) :
    (H.auxType l₀ u₀ u₁).truncate k =
        (H.auxType l₁ v₀ v₁).truncate k ↔
      k ≤ H.toOrdered3Graph.auxMeetLevel u₀ u₁ v₀ v₁ := by
  classical
  have hk₀ : k ≤ l₀ := hk.trans (min_le_left _ _)
  have hk₁ : k ≤ l₁ := hk.trans (min_le_right _ _)
  constructor
  · intro heq
    have hs : H.toOrdered3Graph.SameAuxTypeBelow k u₀ u₁ v₀ v₁ :=
      (H.auxType_crossCut_prefix_eq_iff hk₀ hk₁).mp heq
    have hkbound : k ≤ min u₀ v₀ := le_min (hk₀.trans hlu) (hk₁.trans hlv)
    exact Nat.le_findGreatest hkbound hs
  · intro hkmeet
    apply (H.auxType_crossCut_prefix_eq_iff hk₀ hk₁).mpr
    have hs := H.toOrdered3Graph.auxMeetLevel_agree u₀ u₁ v₀ v₁
    intro a ha
    exact hs (lt_of_lt_of_le ha hkmeet)

/-- The last common prefix of singleton-type nodes over different
levels is exactly min(l0,l1,oneMeet(u,v)). -/
noncomputable def oneTypeCrossCutMeetLevel {N : Nat} (H : EnumNode N)
    (l₀ l₁ u v : Nat) : Nat := by
  classical
  exact Nat.findGreatest
    (fun k => (H.oneType l₀ u).truncate k =
      (H.oneType l₁ v).truncate k) (min l₀ l₁)

/-- Exact common prefix formula for two singleton-type nodes. -/
theorem oneType_greatest_common_prefix
    {N l₀ l₁ u v : Nat} (H : EnumNode N)
    (hlu : l₀ ≤ u) (hlv : l₁ ≤ v) :
    H.oneTypeCrossCutMeetLevel l₀ l₁ u v =
      min (min l₀ l₁) (H.toOrdered3Graph.oneMeetLevel u v) := by
  classical
  unfold oneTypeCrossCutMeetLevel
  let L := min l₀ l₁
  let w := H.toOrdered3Graph.oneMeetLevel u v
  let P : Nat → Prop := fun k =>
    (H.oneType l₀ u).truncate k = (H.oneType l₁ v).truncate k
  have hp0 : P 0 := by
    apply (H.oneType_crossCut_eq_iff_le_meet hlu hlv
      (show 0 ≤ L by omega)).mpr
    exact Nat.zero_le _
  have hspec : P (Nat.findGreatest P L) := by
    exact Nat.findGreatest_spec (m := 0) (n := L) (Nat.zero_le L) hp0
  have hbound : Nat.findGreatest P L ≤ L :=
    Nat.findGreatest_le (P := P) L
  have hmeet : Nat.findGreatest P L ≤ w :=
    (H.oneType_crossCut_eq_iff_le_meet hlu hlv hbound).mp hspec
  have hupper : Nat.findGreatest P L ≤ min L w :=
    le_min hbound hmeet
  have hmin : P (min L w) :=
    (H.oneType_crossCut_eq_iff_le_meet hlu hlv (min_le_left L w)).mpr
      (min_le_right L w)
  have hlower : min L w ≤ Nat.findGreatest P L :=
    Nat.le_findGreatest (min_le_left L w) hmin
  exact Nat.le_antisymm hupper hlower

/-- The auxiliary-type analogue, with the auxiliary meet of the
two ordered pairs determining their first disagreement. -/
noncomputable def auxTypeCrossCutMeetLevel {N : Nat} (H : EnumNode N)
    (l₀ l₁ u₀ u₁ v₀ v₁ : Nat) : Nat := by
  classical
  exact Nat.findGreatest
    (fun k => (H.auxType l₀ u₀ u₁).truncate k =
      (H.auxType l₁ v₀ v₁).truncate k) (min l₀ l₁)

/-- Exact common prefix formula for two auxiliary-type nodes. -/
theorem auxType_greatest_common_prefix
    {N l₀ l₁ u₀ u₁ v₀ v₁ : Nat} (H : EnumNode N)
    (hlu : l₀ ≤ u₀) (hlv : l₁ ≤ v₀) :
    H.auxTypeCrossCutMeetLevel l₀ l₁ u₀ u₁ v₀ v₁ =
      min (min l₀ l₁)
        (H.toOrdered3Graph.auxMeetLevel u₀ u₁ v₀ v₁) := by
  classical
  unfold auxTypeCrossCutMeetLevel
  let L := min l₀ l₁
  let w := H.toOrdered3Graph.auxMeetLevel u₀ u₁ v₀ v₁
  let P : Nat → Prop := fun k =>
    (H.auxType l₀ u₀ u₁).truncate k =
      (H.auxType l₁ v₀ v₁).truncate k
  have hp0 : P 0 := by
    apply (H.auxType_crossCut_eq_iff_le_meet hlu hlv
      (show 0 ≤ L by omega)).mpr
    exact Nat.zero_le _
  have hspec : P (Nat.findGreatest P L) := by
    exact Nat.findGreatest_spec (m := 0) (n := L) (Nat.zero_le L) hp0
  have hbound : Nat.findGreatest P L ≤ L :=
    Nat.findGreatest_le (P := P) L
  have hmeet : Nat.findGreatest P L ≤ w :=
    (H.auxType_crossCut_eq_iff_le_meet hlu hlv hbound).mp hspec
  have hupper : Nat.findGreatest P L ≤ min L w :=
    le_min hbound hmeet
  have hmin : P (min L w) :=
    (H.auxType_crossCut_eq_iff_le_meet hlu hlv (min_le_left L w)).mpr
      (min_le_right L w)
  have hlower : min L w ≤ Nat.findGreatest P L :=
    Nat.le_findGreatest (min_le_left L w) hmin
  exact Nat.le_antisymm hupper hlower

end EnumNode
end ThreeUniformDiaries
