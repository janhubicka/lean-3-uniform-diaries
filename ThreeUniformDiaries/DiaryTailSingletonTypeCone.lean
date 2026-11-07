import ThreeUniformDiaries.ExactTypeMeetLevels

/-!
# A bounded singleton-type cone preserves all earlier leaf meets

Fix a cut B and two vertices v,w whose singleton types agree BELOW
B, i.e., every increasing test (x,y) with y<B has the same edge bit
to v and w. For any earlier a<B with a<v,w, the capped singleton
meets with a are then literally equal:
  K.oneMeetLevel a v = K.oneMeetLevel a w.

Unlike a vague "genericity" argument, this requires exactly the
actual mixed test equality of the two candidates, not merely that
their leaf-only reducts are isomorphic. No target leaf realization
or infinite source embedding is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A common singleton type below B fixes all edges from any
two earlier test vertices with second test coordinate below B. -/
theorem edge_iff_of_sameOneTypeBelow_cut
    (K : Ordered3Graph Nat) (B x y u v : Nat)
    (hxy : x < y) (hyB : y < B)
    (hSame : K.SameOneTypeBelow B u v) :
    (K.edge x y u ↔ K.edge x y v) :=
  hSame hxy hyB

/-- Replacing one future leaf by a singleton-type-equivalent one
does not change its exact capped singleton meet with an old vertex
below the cut. All comparisons of old/new types take place at
testing levels below the old vertex, hence below the cut. -/
theorem oneMeetLevel_eq_of_sameOneTypeBelow_cut
    (K : Ordered3Graph Nat) (B a u v : Nat)
    (haB : a < B) (hau : a < u) (hav : a < v)
    (hSame : K.SameOneTypeBelow B u v) :
    K.oneMeetLevel a u = K.oneMeetLevel a v := by
  classical
  have hPre (l : Nat) (hl : l ≤ a) :
      K.SameOneTypeBelow l a u ↔
        K.SameOneTypeBelow l a v := by
    constructor
    · intro h x y hxy hyl
      have hyB : y < B := lt_of_lt_of_le hyl (hl.trans haB.le)
      exact (h hxy hyl).trans (hSame hxy hyB)
    · intro h x y hxy hyl
      have hyB : y < B := lt_of_lt_of_le hyl (hl.trans haB.le)
      exact (h hxy hyl).trans (hSame hxy hyB).symm
  have hU : K.oneMeetLevel a u ≤ a :=
    (K.oneMeetLevel_le_min a u).trans (min_le_left _ _)
  have hV : K.oneMeetLevel a v ≤ a :=
    (K.oneMeetLevel_le_min a v).trans (min_le_left _ _)
  have hUV : K.oneMeetLevel a u ≤ K.oneMeetLevel a v := by
    apply Nat.le_findGreatest
      (by simpa only [min_eq_left hav.le] using hU)
    exact (hPre _ hU).mp (K.oneMeetLevel_agree a u)
  have hVU : K.oneMeetLevel a v ≤ K.oneMeetLevel a u := by
    apply Nat.le_findGreatest
      (by simpa only [min_eq_left hau.le] using hV)
    exact (hPre _ hV).mpr (K.oneMeetLevel_agree a v)
  exact Nat.le_antisymm hUV hVU

end DiaryLeafPriority
end ThreeUniformDiaries
