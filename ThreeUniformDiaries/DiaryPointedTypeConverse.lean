import ThreeUniformDiaries.DiaryRoleEnvelopeAssembly

/-!
# Reconstructing a full 2-type from an induced pointed picture

The converse of the pointed-envelope type-profile theorem is
elementary but important: equality of *all* induced triples on a
full prefix plus the two distinguished endpoints recovers both
coordinate singleton profiles and their auxiliary pair profile.
This remains true when the selected target enumerations skip levels.

Combining this with the previously checked forward diary argument
gives the literal two-tail/three-tail pointed-shape equivalences.
No blanket auxiliary meet preservation is assumed.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- A full prefix and two distinguished selected vertices recover
their complete ordinary 2-type solely from the induced edges.
The two distinguished positions need not be adjacent in the
enumeration, and no target image convexity is assumed. -/
theorem sameTwoTypeBelow_of_pointed_edge_agreement
    (K : Ordered3Graph Nat) (f g : Nat → Nat)
    (j p q : Nat) (hjp : j ≤ p) (hpq : p < q)
    (hfixf : ∀ t, t < j → f t = t)
    (hfixg : ∀ t, t < j → g t = t)
    (hedge : ∀ x y z, x < y → y < z → z < q+1 →
      (K.pullback f).edge x y z ↔ (K.pullback g).edge x y z) :
    K.SameTwoTypeBelow j (f p) (f q) (g p) (g q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy hyj
    have hxj : x < j := lt_trans hxy hyj
    have hyp : y < p := lt_of_lt_of_le hyj hjp
    have h := hedge x y p hxy hyp (by omega)
    change K.edge (f x) (f y) (f p) ↔
      K.edge (g x) (g y) (g p) at h
    simpa only [hfixf x hxj, hfixf y hyj,
      hfixg x hxj, hfixg y hyj] using h
  · intro x y hxy hyj
    have hxj : x < j := lt_trans hxy hyj
    have hyq : y < q := lt_of_lt_of_le (lt_of_lt_of_le hyj hjp) hpq.le
    have h := hedge x y q hxy hyq (by omega)
    change K.edge (f x) (f y) (f q) ↔
      K.edge (g x) (g y) (g q) at h
    simpa only [hfixf x hxj, hfixf y hyj,
      hfixg x hxj, hfixg y hyj] using h
  · intro z hz
    have hzp : z < p := lt_of_lt_of_le hz hjp
    have h := hedge z p q hzp hpq (by omega)
    change K.edge (f z) (f p) (f q) ↔
      K.edge (g z) (g p) (g q) at h
    simpa only [hfixf z hz, hfixg z hz] using h

/-- The induced prefix-plus-two-tail pictures agree if and only if
the two ordered source pairs have identical full 2-types. This
equivalence is valid for any type-respecting embedding, not only
for diaries. -/
theorem two_tail_picture_equal_iff_source_pair_type
    {H K : Ordered3Graph Nat}
    (ψ : Embedding H K) (hψ : ψ.TypeRespecting)
    (i a b c d : Nat)
    (hia : i ≤ a) (hic : i ≤ c)
    (hab : a < b) (hcd : c < d) :
    ( (∀ x y z, x < y → y < z → z < ψ i + 2 →
        (K.pullback (twoTailInsertion (ψ i) (ψ a) (ψ b))).edge x y z ↔
        (K.pullback (twoTailInsertion (ψ i) (ψ c) (ψ d))).edge x y z)
      ↔ H.SameTwoTypeBelow i a b c d ) := by
  let f := twoTailInsertion (ψ i) (ψ a) (ψ b)
  let g := twoTailInsertion (ψ i) (ψ c) (ψ d)
  have hfixf : ∀ t, t < ψ i → f t = t := by
    intro t ht
    exact twoTailInsertion_fix_prefix (ψ i) (ψ a) (ψ b) t ht
  have hfixg : ∀ t, t < ψ i → g t = t := by
    intro t ht
    exact twoTailInsertion_fix_prefix (ψ i) (ψ c) (ψ d) t ht
  have hfA : f (ψ i) = ψ a :=
    twoTailInsertion_first (ψ i) (ψ a) (ψ b)
  have hfB : f (ψ i+1) = ψ b :=
    twoTailInsertion_second (ψ i) (ψ a) (ψ b)
  have hgC : g (ψ i) = ψ c :=
    twoTailInsertion_first (ψ i) (ψ c) (ψ d)
  have hgD : g (ψ i+1) = ψ d :=
    twoTailInsertion_second (ψ i) (ψ c) (ψ d)
  constructor
  · intro hedge
    have hImage := K.sameTwoTypeBelow_of_pointed_edge_agreement
      f g (ψ i) (ψ i) (ψ i+1)
      (by omega) (by omega) hfixf hfixg hedge
    have hImage' : K.SameTwoTypeBelow (ψ i)
        (ψ a) (ψ b) (ψ c) (ψ d) := by
      simpa only [hfA, hfB, hgC, hgD] using hImage
    exact (hψ.two i a b c d hia hab hic hcd).mpr hImage'
  · intro hpair x y z hxy hyz hz
    exact K.pointed_two_tail_shapes_after_type_embedding
      ψ hψ i a b c d hia hic hab hcd hpair
      f g hfixf hfixg hfA hfB hgC hgD x y z hxy hyz hz

/-- Equality of three-tail induced pictures reconstructs the full
source 2-type of the distinguished final leaf pairs. This is
independent of diary-specific role or marker axioms. -/
theorem three_tail_picture_equal_implies_source_pair_type
    {H K : Ordered3Graph Nat}
    (ψ : Embedding H K) (hψ : ψ.TypeRespecting)
    (i m n a b c d : Nat)
    (hia : i ≤ a) (hic : i ≤ c)
    (hab : a < b) (hcd : c < d)
    (hedge : ∀ x y z, x < y → y < z → z < ψ i + 3 →
      (K.pullback (threeTailInsertion (ψ i) (ψ m) (ψ a) (ψ b))).edge x y z ↔
      (K.pullback (threeTailInsertion (ψ i) (ψ n) (ψ c) (ψ d))).edge x y z) :
    H.SameTwoTypeBelow i a b c d := by
  let f := threeTailInsertion (ψ i) (ψ m) (ψ a) (ψ b)
  let g := threeTailInsertion (ψ i) (ψ n) (ψ c) (ψ d)
  have hfixf : ∀ t, t < ψ i → f t = t := by
    intro t ht
    exact threeTailInsertion_fix_prefix (ψ i) (ψ m) (ψ a) (ψ b) t ht
  have hfixg : ∀ t, t < ψ i → g t = t := by
    intro t ht
    exact threeTailInsertion_fix_prefix (ψ i) (ψ n) (ψ c) (ψ d) t ht
  have hImage := K.sameTwoTypeBelow_of_pointed_edge_agreement
    f g (ψ i) (ψ i+1) (ψ i+2)
    (by omega) (by omega) hfixf hfixg hedge
  have hImage' : K.SameTwoTypeBelow (ψ i)
      (ψ a) (ψ b) (ψ c) (ψ d) := by
    simpa only [threeTailInsertion_first, threeTailInsertion_second] using hImage
  exact (hψ.two i a b c d hia hab hic hcd).mpr hImage'

end Ordered3Graph

namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph

/-- In the three-tail case, equality of the complete induced
pointed pictures is equivalent to equality of the source leaf
pair's full 2-type. All marker orientation hypotheses are now
consequences of the single role-based diary definition. -/
theorem three_tail_picture_equal_iff_source_leaf_pair_type
    {H K : Ordered3Graph Nat}
    (D : RoleDiary H)
    (ψ : Ordered3Graph.Embedding H K) (hψ : ψ.TypeRespecting)
    (i a b c d : Nat) (hi : 3 ≤ i)
    (hia : i ≤ a) (hic : i ≤ c)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hcase : i ≤ H.oneMeetLevel a b) :
    ( (∀ x y z, x < y → y < z → z < ψ i + 3 →
        (K.pullback (threeTailInsertion
          (ψ i) (ψ (H.oneMeetLevel a b)) (ψ a) (ψ b))).edge x y z ↔
        (K.pullback (threeTailInsertion
          (ψ i) (ψ (H.oneMeetLevel c d)) (ψ c) (ψ d))).edge x y z)
      ↔ H.SameTwoTypeBelow i a b c d ) := by
  constructor
  · intro hshape
    exact Ordered3Graph.three_tail_picture_equal_implies_source_pair_type
      ψ hψ i (H.oneMeetLevel a b) (H.oneMeetLevel c d)
      a b c d hia hic hab hcd hshape
  · intro hpair x y z hxy hyz hz
    exact D.pointed_three_tail_shapes_of_same_leaf_two_type
      ψ hψ i a b c d hi hia hic hab hcd
      ha hb hc hd hpair hcase x y z hxy hyz hz

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
