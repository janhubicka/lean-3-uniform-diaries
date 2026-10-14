import ThreeUniformDiaries.DiaryEdgeShapeWitness

/-!
# Exact singleton meets under ordinary type-respecting embeddings

Selected-cut agreement alone might appear weaker than preservation of
the *numerical* singleton meet if an embedding skips target indices.
The missing upper bound comes from the first disagreement at the
source meet, an actual hyperedge comparison transported by inducedness.
This is independent of any diary axiom.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- A disagreement in the last coordinate at the edge (x,y,-)
bounds the singleton type meet by y. -/
theorem oneMeetLevel_le_of_edge_disagreement
    (H : Ordered3Graph Nat) (u v x y : Nat)
    (hxy : x < y)
    (hdiff : ¬ (H.edge x y u ↔ H.edge x y v)) :
    H.oneMeetLevel u v ≤ y := by
  by_contra hn
  have hy : y < H.oneMeetLevel u v := Nat.lt_of_not_ge hn
  exact hdiff ((H.oneMeetLevel_agree u v) hxy hy)

/-- Exact capped singleton meets are preserved by an induced
type-respecting embedding, even when its image is non-convex.
The source's first-disagreement edge witnesses the upper bound. -/
theorem typeRespecting_oneMeetLevel_eq
    {H K : Ordered3Graph Nat}
    (ψ : Embedding H K) (hψ : ψ.TypeRespecting)
    (u v : Nat) :
    K.oneMeetLevel (ψ u) (ψ v) =
      ψ (H.oneMeetLevel u v) := by
  classical
  let w := H.oneMeetLevel u v
  have hbound : w ≤ min u v := H.oneMeetLevel_le_min u v
  have hwu : w ≤ u := hbound.trans (min_le_left _ _)
  have hwv : w ≤ v := hbound.trans (min_le_right _ _)
  have hagree : H.SameOneTypeBelow w u v := H.oneMeetLevel_agree u v
  have himage : K.SameOneTypeBelow (ψ w) (ψ u) (ψ v) :=
    (hψ.one w u v hwu hwv).mp hagree
  have hlow : ψ w ≤ K.oneMeetLevel (ψ u) (ψ v) :=
    Nat.le_findGreatest
      (le_min (ψ.strictMono.monotone hwu)
        (ψ.strictMono.monotone hwv)) himage
  by_cases hcap : w = min u v
  · have hmin : min (ψ u) (ψ v) = ψ (min u v) := by
      rcases le_total u v with huv | hvu
      · simp [min_eq_left huv, min_eq_left (ψ.strictMono.monotone huv)]
      · simp [min_eq_right hvu, min_eq_right (ψ.strictMono.monotone hvu)]
    have hupper : K.oneMeetLevel (ψ u) (ψ v) ≤ ψ w := by
      rw [hcap, ← hmin]
      exact K.oneMeetLevel_le_min (ψ u) (ψ v)
    exact Nat.le_antisymm hupper hlow
  · have hstrict : w < min u v := by omega
    have hwu' : w < u := lt_of_lt_of_le hstrict (min_le_left _ _)
    have hwv' : w < v := lt_of_lt_of_le hstrict (min_le_right _ _)
    obtain ⟨z, hzw, hdiff⟩ :=
      DiaryLeafPriority.oneMeetLevel_has_first_witness H u v w
        rfl hwu' hwv'
    have hedgeU : H.edge z w u ↔ K.edge (ψ z) (ψ w) (ψ u) :=
      ψ.edge_iff hzw hwu'
    have hedgeV : H.edge z w v ↔ K.edge (ψ z) (ψ w) (ψ v) :=
      ψ.edge_iff hzw hwv'
    have hdiffImage :
        ¬ (K.edge (ψ z) (ψ w) (ψ u) ↔
           K.edge (ψ z) (ψ w) (ψ v)) := by
      intro hK
      exact hdiff (hedgeU.trans (hK.trans hedgeV.symm))
    have hupper : K.oneMeetLevel (ψ u) (ψ v) ≤ ψ w :=
      K.oneMeetLevel_le_of_edge_disagreement
        (ψ u) (ψ v) (ψ z) (ψ w) (ψ.strictMono hzw) hdiffImage
    exact Nat.le_antisymm hupper hlow

end Ordered3Graph
end ThreeUniformDiaries
