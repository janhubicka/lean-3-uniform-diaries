import ThreeUniformDiaries.DiaryFullRoleDefinition

/-!
# Exact successor singleton types at a diary one-split

The five permitted edge shapes imply that among the bits added to
a singleton type at a one-split m, every bit edge(z,m,v) with
0 < z < m vanishes for a leaf v. Only the split/leaf marker
edge(0,m,v) can change. Together with V1 coherence this identifies
the entire positive witness class through cut m+1, as required
for stabilised one-split pre-embedding witness independence.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

variable {H : Ordered3Graph Nat} (D : RoleDiary H)

/-- Moving the singleton type cut through a diary one-split adds
ONLY the marker bit edge(0,m,v). -/
theorem sameOneTypeBelow_succ_iff_of_oneSplit
    (m u v : Nat)
    (hm : IsOneSplit H m)
    (hu : IsLeaf H u) (hv : IsLeaf H v) :
    H.SameOneTypeBelow (m+1) u v ↔
      H.SameOneTypeBelow m u v ∧
      (H.edge 0 m u ↔ H.edge 0 m v) := by
  rw [H.sameOneTypeBelow_succ_iff m u v]
  constructor
  · rintro ⟨hbelow, hbits⟩
    have hzero : 0 < m := by
      have hbound := hm.1
      omega
    exact ⟨hbelow, hbits 0 hzero⟩
  · rintro ⟨hbelow, hmarker⟩
    constructor
    · exact hbelow
    · intro z hz
      by_cases hz0 : z = 0
      · subst z
        exact hmarker
      · exact iff_of_false
          (D.splitEdgeShape.oneSplit_earlier_only_zero
            m u z hm hu hz hz0)
          (D.splitEdgeShape.oneSplit_earlier_only_zero
            m v z hm hv hz hz0)

/-- Two leaves on the positive side of a diary one-split share
their complete singleton type through the successor cut. -/
theorem oneSplit_incident_oneTypes_succ
    (m u v : Nat)
    (hm : IsOneSplit H m)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (heu : H.edge 0 m u) (hev : H.edge 0 m v) :
    H.SameOneTypeBelow (m+1) u v := by
  apply (D.sameOneTypeBelow_succ_iff_of_oneSplit m u v hm hu hv).2
  exact ⟨D.one_split_coherent m u v hm hu hv heu hev,
    ⟨fun _ => hev, fun _ => heu⟩⟩

/-- A genuine singleton meet at one-split m is witnessed by
OPPOSITE zero-marker edge bits. -/
theorem oneSplit_witness_opposite_marker
    (m u v : Nat)
    (hm : IsOneSplit H m)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m < u) (hmv : m < v)
    (hmeet : H.oneMeetLevel u v = m) :
    ¬ (H.edge 0 m u ↔ H.edge 0 m v) := by
  have hbranch := oneSplit_branch_zero H D.splitEdgeShape
    m u v hu hv hm hmeet hmu hmv
  rcases hbranch with ⟨heu, hnotv⟩ | ⟨hnotu, hev⟩
  · intro he
    exact hnotv (he.mp heu)
  · intro he
    exact hnotu (he.mpr hev)

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
