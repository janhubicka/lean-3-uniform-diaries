import ThreeUniformDiaries.DiaryOnePassEventTestCensus
import ThreeUniformDiaries.DiaryOnePassDelayedPairGermFactor
import ThreeUniformDiaries.DiaryOnePassIndexCoverage

/-!
# No new singleton-type distinction at an old leaf's target column

The static one-pass completion inserts pair events at earlier original
cuts. Some of their edges become singleton tests only when a later
ORIGINAL LEAF m appears in the middle coordinate:
  E(event, f(m), f(u)).

The critical delayed-test condition is that these extra edges are
already functions of the ORIGINAL next-cut singleton type s_(m+1)(u).
We prove this for the ENTIRE genuine target column f(m), not merely
for a previously named event.

For any original leaf m and original leaves u,v strictly above m,
equality of their original singleton (m+1)-codes implies that
EVERY possible first-coordinate target edge into (f(m),f(u)) and
(f(m),f(v)) agrees. An earlier target first coordinate is either:

* an original vertex f(k), k<m, controlled by the source singleton
  code through m+1 and induced-edge reflection; or
* a fresh event e in block B_r, r<=m. For a pair event the delayed
  full-pair germ factors through s_(m+1), and for a singleton event
  all first-coordinate edges are forbidden by the target E axiom.

The proof includes pair events in B_m and capped terminal pairs.
This is the nonlocal OLD LEAF step needed after the local block
type transport. It is not the global prefix induction itself.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

variable {H : Ordered3Graph Nat}

/-- An original source leaf column f(m) cannot distinguish two
later original leaves with the same ORIGINAL (m+1)-singleton code,
even using any earlier fresh event as its first coordinate. -/
theorem onePass_oldLeaf_column_stable_of_nextOneCode
    (P : RolePrediary H) (m u v : Nat)
    (hm : IsLeaf H m) (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m < u) (hmv : m < v)
    (hcode : oneCode H (m + 1) u = oneCode H (m + 1) v) :
    ∀ z : Nat, z < onePassOldImage H m →
      ((onePassRawTarget H).edge z
         (onePassOldImage H m) (onePassOldImage H u) ↔
       (onePassRawTarget H).edge z
         (onePassOldImage H m) (onePassOldImage H v)) := by
  intro z hz
  rcases onePass_target_index_covered H z with
      ⟨k, hk⟩ | ⟨r, i, hr⟩
  · have hkm : k < m := by
      by_contra hnot
      have hmk : m ≤ k := by omega
      have hmono := (onePassOldImage_strictMono H).monotone hmk
      omega
    have htype : H.SameOneTypeBelow (m + 1) u v :=
      (oneCode_eq_iff_sameOneType H (m + 1) u v).mp hcode
    have hOriginal : H.edge k m u ↔ H.edge k m v :=
      htype hkm (by omega)
    have hU := onePassRawTarget_edge_image_iff H k m u
    have hV := onePassRawTarget_edge_image_iff H k m v
    rw [← hk]
    exact hU.trans (hOriginal.trans hV.symm)
  · have hrm : r ≤ m := by
      by_contra hnot
      have hmr : m < r := by omega
      have hsep := onePassOldImage_lt_before H m r hmr
      have hstart := (onePassEventPosition_interval H r i).1
      omega
    rw [← hr]
    rcases onePass_event_label_at_own_cut H r i with
        ⟨g, hPair⟩ | ⟨g, hOne⟩
    · exact onePassPairEvent_delayed_singleton_test_agrees
        H r m u v i g hPair hrm hmu hmv hm hu hv hcode
    · exact iff_of_false
        (onePassRawTarget_freshOne_no_aux_test P r i g hOne
          (onePassOldImage H m) (onePassOldImage H u))
        (onePassRawTarget_freshOne_no_aux_test P r i g hOne
          (onePassOldImage H m) (onePassOldImage H v))

/-- The same no-new-distinction statement in the source
one-type relation rather than finite Boolean code equality. -/
theorem onePass_oldLeaf_column_stable_of_nextOneType
    (P : RolePrediary H) (m u v : Nat)
    (hm : IsLeaf H m) (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m < u) (hmv : m < v)
    (hnext : H.SameOneTypeBelow (m + 1) u v) :
    ∀ z : Nat, z < onePassOldImage H m →
      ((onePassRawTarget H).edge z
         (onePassOldImage H m) (onePassOldImage H u) ↔
       (onePassRawTarget H).edge z
         (onePassOldImage H m) (onePassOldImage H v)) :=
  onePass_oldLeaf_column_stable_of_nextOneCode P m u v
    hm hu hv hmu hmv
    ((oneCode_eq_iff_sameOneType H (m + 1) u v).mpr hnext)

end DiaryLeafPriority
end ThreeUniformDiaries
