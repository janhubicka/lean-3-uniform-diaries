import ThreeUniformDiaries.CanonicalInfiniteImage
import ThreeUniformDiaries.PrefixMeetInvariance
import ThreeUniformDiaries.CanonicalExactMeets

/-!
# Exact capped meets for the coherent infinite canonical image

The checked finite canonical-map theorem preserves both singleton and
auxiliary capped meets. The coherent infinite target is a union of
mapped finite prefixes. The finite-cut invariance lemmas show that
these exact meet values cannot change when larger target prefixes
are added.

Together this closes literal capped-meet preservation for the
canonical level embedding into its ACTUAL countable image graph,
including skipped ambient indices. No gap-inheritance, finiteness
or further embedding hypotheses are imposed.
-/

namespace ThreeUniformDiaries
namespace CanonicalMap

/-- The actual infinite image of a canonical map has precisely the
image of each source singleton capped meet. -/
theorem imageGraph_oneMeetLevel_preserved
    (F : CanonicalMap) (H : Ordered3Graph Nat)
    (u v : Nat) :
    (F.imageGraph H).oneMeetLevel (F.level u) (F.level v) =
      F.level (H.oneMeetLevel u v) := by
  let N := max u v + 1
  have hu : u < N := by dsimp [N]; omega
  have hv : v < N := by dsimp [N]; omega
  have hfu : F.level u < F.level N := F.strictMono hu
  have hfv : F.level v < F.level N := F.strictMono hv
  have htarget :=
    (F.imageGraph H).initialSegment_oneMeetLevel
      (F.level N) (F.level u) (F.level v) hfu hfv
  have hfinite :=
    F.oneMeetLevel_preserved_on_finite
      (H.initialSegment N) u v hu hv
  have hsource :=
    H.initialSegment_oneMeetLevel N u v hu hv
  calc
    (F.imageGraph H).oneMeetLevel (F.level u) (F.level v) =
        ((F.imageGraph H).initialSegment
          (F.level N)).toOrdered3Graph.oneMeetLevel
          (F.level u) (F.level v) :=
      htarget.symm
    _ = (F.mapEnum N (H.initialSegment N)).toOrdered3Graph.oneMeetLevel
          (F.level u) (F.level v) := by
      rw [F.imageGraph_initialSegment_eq H N]
    _ = F.level ((H.initialSegment N).toOrdered3Graph.oneMeetLevel u v) :=
      hfinite
    _ = F.level (H.oneMeetLevel u v) := by rw [hsource]

/-- Likewise, both increasing source pairs have their precise
capped auxiliary meet preserved in the countable image hypergraph. -/
theorem imageGraph_auxMeetLevel_preserved
    (F : CanonicalMap) (H : Ordered3Graph Nat)
    (u₀ u₁ v₀ v₁ : Nat)
    (hu : u₀ < u₁) (hv : v₀ < v₁) :
    (F.imageGraph H).auxMeetLevel
      (F.level u₀) (F.level u₁) (F.level v₀) (F.level v₁) =
      F.level (H.auxMeetLevel u₀ u₁ v₀ v₁) := by
  let N := max u₁ v₁ + 1
  have huN : u₁ < N := by dsimp [N]; omega
  have hvN : v₁ < N := by dsimp [N]; omega
  have hfu : F.level u₁ < F.level N := F.strictMono huN
  have hfv : F.level v₁ < F.level N := F.strictMono hvN
  have htarget :=
    (F.imageGraph H).initialSegment_auxMeetLevel
      (F.level N) (F.level u₀) (F.level u₁)
      (F.level v₀) (F.level v₁)
      (F.strictMono hu) hfu (F.strictMono hv) hfv
  have hfinite :=
    F.auxMeetLevel_preserved_on_finite
      (H.initialSegment N) u₀ u₁ v₀ v₁ hu huN hv hvN
  have hsource :=
    H.initialSegment_auxMeetLevel N
      u₀ u₁ v₀ v₁ hu huN hv hvN
  calc
    (F.imageGraph H).auxMeetLevel
        (F.level u₀) (F.level u₁) (F.level v₀) (F.level v₁) =
        ((F.imageGraph H).initialSegment
          (F.level N)).toOrdered3Graph.auxMeetLevel
          (F.level u₀) (F.level u₁) (F.level v₀) (F.level v₁) :=
      htarget.symm
    _ = (F.mapEnum N (H.initialSegment N)).toOrdered3Graph.auxMeetLevel
          (F.level u₀) (F.level u₁) (F.level v₀) (F.level v₁) := by
      rw [F.imageGraph_initialSegment_eq H N]
    _ = F.level ((H.initialSegment N).toOrdered3Graph.auxMeetLevel
          u₀ u₁ v₀ v₁) := hfinite
    _ = F.level (H.auxMeetLevel u₀ u₁ v₀ v₁) := by rw [hsource]

end CanonicalMap
end ThreeUniformDiaries
