import ThreeUniformDiaries.DiaryEmbeddingExactOneMeets
import ThreeUniformDiaries.DiaryPointedATRFinite

/-!
# The complete three-tail ATR interface from actual diary role markers

This replaces the abstract three-marker hypotheses by the concrete
split and leaf roles, (S1) singleton split, and the restricted E/V
edge-shape conditions. Markers 0,1,2 are transported by a
type-respecting embedding; they may lie at non-consecutive target
indices inside the full protected prefix.

The conclusion is a finite-carrier auxiliary meet-preservation
statement for any strictly increasing selected enumeration. The
remaining separate obligation is to identify the canonical *minimal*
type envelope with precisely this selected carrier.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Source role bits force the singleton meets of a split and either
child leaf to occur by marker 1 in every type-respecting image. -/
theorem oneSplit_mixed_meets_early_in_image
    {H K : Ordered3Graph Nat}
    (ψ : Ordered3Graph.Embedding H K) (hψ : ψ.TypeRespecting)
    (i m a b : Nat)
    (hi : 3 ≤ i) (him : i ≤ m)
    (hm : IsOneSplit H m)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hma : m < a) (hmb : m < b) :
    K.oneMeetLevel (ψ m) (ψ a) < ψ i ∧
    K.oneMeetLevel (ψ m) (ψ b) < ψ i := by
  have hdiffA : ¬ (H.edge 0 1 m ↔ H.edge 0 1 a) := by
    intro h
    exact ha.2.1 (h.mp hm.2.1)
  have hdiffB : ¬ (H.edge 0 1 m ↔ H.edge 0 1 b) := by
    intro h
    exact hb.2.1 (h.mp hm.2.1)
  have hmeeta : H.oneMeetLevel m a ≤ 1 :=
    H.oneMeetLevel_le_of_edge_disagreement m a 0 1 (by omega) hdiffA
  have hmeetb : H.oneMeetLevel m b ≤ 1 :=
    H.oneMeetLevel_le_of_edge_disagreement m b 0 1 (by omega) hdiffB
  constructor
  · calc
      K.oneMeetLevel (ψ m) (ψ a) =
        ψ (H.oneMeetLevel m a) :=
          Ordered3Graph.typeRespecting_oneMeetLevel_eq ψ hψ m a
      _ ≤ ψ 1 := ψ.strictMono.monotone hmeeta
      _ < ψ i := ψ.strictMono (by omega)
  · calc
      K.oneMeetLevel (ψ m) (ψ b) =
        ψ (H.oneMeetLevel m b) :=
          Ordered3Graph.typeRespecting_oneMeetLevel_eq ψ hψ m b
      _ ≤ ψ 1 := ψ.strictMono.monotone hmeetb
      _ < ψ i := ψ.strictMono (by omega)

/-- Every role-based 1-split and its two leaf children gives a
genuine ATR-admissible selected three-tail carrier in an arbitrary
type-respecting image, even across omitted target levels.

The prefix [0,ψ i) is fixed by f; its three exterior vertices are
exactly ψ m, ψ a, ψ b. Equality of the leaf meet with m and all
the necessary marker disagreements follow from the source
diary hypotheses rather than being assumed in the target. -/
theorem oneSplit_three_tail_ATR_after_type_embedding
    {H K : Ordered3Graph Nat}
    (shape : SplitEdgeShape H)
    (ψ : Ordered3Graph.Embedding H K) (hψ : ψ.TypeRespecting)
    (i m a b : Nat)
    (hi : 3 ≤ i) (him : i ≤ m)
    (hm : IsOneSplit H m)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hab : a < b) (hma : m < a)
    (hmeet : H.oneMeetLevel a b = m)
    (f : Nat → Nat) (hf : StrictMono f)
    (hfix : ∀ t, t < ψ i → f t = t)
    (hfM : f (ψ i) = ψ m)
    (hfA : f (ψ i + 1) = ψ a)
    (hfB : f (ψ i + 2) = ψ b) :
    (∀ u v, u < ψ i + 3 → v < ψ i + 3 →
      K.oneMeetLevel (f u) (f v) =
        f ((K.pullback f).oneMeetLevel u v)) ∧
    (∀ c d e g, c < d → e < g →
      d < ψ i + 3 → g < ψ i + 3 →
      K.auxMeetLevel (f c) (f d) (f e) (f g) =
        f ((K.pullback f).auxMeetLevel c d e g)) := by
  have hmb : m < b := lt_trans hma hab
  have hm0 : 0 < m := by have ht := hm.1; omega
  have hm1 : 1 < m := by have ht := hm.1; omega
  have hm2 : 2 < m := by have ht := hm.1; omega
  have h1a : 1 < a := lt_trans hm1 hma
  have h2a : 2 < a := lt_trans hm2 hma
  have honeImage :=
    oneSplit_mixed_meets_early_in_image ψ hψ i m a b
      hi him hm ha hb hma hmb
  have hleafImage : K.oneMeetLevel (ψ a) (ψ b) = ψ m := by
    simpa only [hmeet] using
      (Ordered3Graph.typeRespecting_oneMeetLevel_eq ψ hψ a b)
  have hbranchSource :=
    oneSplit_branch_zero H shape m a b ha hb hm hmeet hma hmb
  have h0a : H.edge 0 m a ↔
      K.edge (ψ 0) (ψ m) (ψ a) := ψ.edge_iff hm0 hma
  have h0b : H.edge 0 m b ↔
      K.edge (ψ 0) (ψ m) (ψ b) := ψ.edge_iff hm0 hmb
  have hbranchImage :
      (K.edge (ψ 0) (ψ m) (ψ a) ∧
       ¬ K.edge (ψ 0) (ψ m) (ψ b)) ∨
      (¬ K.edge (ψ 0) (ψ m) (ψ a) ∧
       K.edge (ψ 0) (ψ m) (ψ b)) := by
    rcases hbranchSource with ⟨hea, hnb⟩ | ⟨hna, heb⟩
    · exact Or.inl ⟨h0a.mp hea, fun h => hnb (h0b.mpr h)⟩
    · exact Or.inr ⟨(fun h => hna (h0a.mpr h)), h0b.mp heb⟩
  have hmarkSource := shape.leaf_pair_marker a b hab ha hb
  have h1ab : H.edge 1 a b ↔
      K.edge (ψ 1) (ψ a) (ψ b) := ψ.edge_iff h1a hab
  have h2ab : H.edge 2 a b ↔
      K.edge (ψ 2) (ψ a) (ψ b) := ψ.edge_iff h2a hab
  have hmarkerImage :
      K.edge (ψ 1) (ψ a) (ψ b) ∨
      K.edge (ψ 2) (ψ a) (ψ b) := by
    rcases hmarkSource with h1 | h2
    · exact Or.inl (h1ab.mp h1)
    · exact Or.inr (h2ab.mp h2)
  have hno1a : ¬ K.edge (ψ 1) (ψ m) (ψ a) := by
    intro h
    have hs := shape.oneSplit_earlier_only_zero m a 1 hm ha hm1 (by omega)
    exact hs ((ψ.edge_iff hm1 hma).mpr h)
  have hno2a : ¬ K.edge (ψ 2) (ψ m) (ψ a) := by
    intro h
    have hs := shape.oneSplit_earlier_only_zero m a 2 hm ha hm2 (by omega)
    exact hs ((ψ.edge_iff hm2 hma).mpr h)
  have hno1b : ¬ K.edge (ψ 1) (ψ m) (ψ b) := by
    intro h
    have hs := shape.oneSplit_earlier_only_zero m b 1 hm hb hm1 (by omega)
    exact hs ((ψ.edge_iff hm1 hmb).mpr h)
  have hno2b : ¬ K.edge (ψ 2) (ψ m) (ψ b) := by
    intro h
    have hs := shape.oneSplit_earlier_only_zero m b 2 hm hb hm2 (by omega)
    exact hs ((ψ.edge_iff hm2 hmb).mpr h)
  have h0i : ψ 0 < ψ i := ψ.strictMono (by omega)
  have h1i : ψ 1 < ψ i := ψ.strictMono (by omega)
  have h2i : ψ 2 < ψ i := ψ.strictMono (by omega)
  have honeA : K.oneMeetLevel (f (ψ i)) (f (ψ i + 1)) < ψ i := by
    simpa only [hfM, hfA] using honeImage.1
  have honeB : K.oneMeetLevel (f (ψ i)) (f (ψ i + 2)) < ψ i := by
    simpa only [hfM, hfB] using honeImage.2
  have hleaf : K.oneMeetLevel (f (ψ i + 1)) (f (ψ i + 2)) =
      f (ψ i) := by
    simpa only [hfA, hfB, hfM] using hleafImage
  have hbranch :
      (K.edge (ψ 0) (f (ψ i)) (f (ψ i + 1)) ∧
       ¬ K.edge (ψ 0) (f (ψ i)) (f (ψ i + 2))) ∨
      (¬ K.edge (ψ 0) (f (ψ i)) (f (ψ i + 1)) ∧
       K.edge (ψ 0) (f (ψ i)) (f (ψ i + 2))) := by
    simpa only [hfM, hfA, hfB] using hbranchImage
  have hmarker :
      K.edge (ψ 1) (f (ψ i + 1)) (f (ψ i + 2)) ∨
      K.edge (ψ 2) (f (ψ i + 1)) (f (ψ i + 2)) := by
    simpa only [hfA, hfB] using hmarkerImage
  exact K.pointed_three_tail_ATR_finite
    f hf (ψ i) (ψ 0) (ψ 1) (ψ 2)
    hfix h0i h1i h2i honeA honeB hleaf
    hbranch hmarker
    (by simpa only [hfM, hfA] using hno1a)
    (by simpa only [hfM, hfA] using hno2a)
    (by simpa only [hfM, hfB] using hno1b)
    (by simpa only [hfM, hfB] using hno2b)

end DiaryLeafPriority
end ThreeUniformDiaries
