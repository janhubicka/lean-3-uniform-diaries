import ThreeUniformDiaries.DiaryFusedThreeTailPairs

/-!
# Full fused pair-type stabilisation for diary leaf pairs

Every ordered pair of distinct leaves of a full role-based diary
has a singleton 1-split meet. Relative to a protected cut i≥3
there are exactly two cases: the split lies before i (two-tail
pointed envelope) or at/after i (three-tail pointed envelope).
Equality of full leaf-pair 2-types forces both pairs to belong
to the same case.

The concrete two-tail and corrected role-based three-tail finite
ATR arguments are already proved separately. Their case split now
gives one theorem with the EXACT pair-type and lexicographic
orientation conclusion required by the lower-bound application,
even after an arbitrary gappy type-respecting embedding into the
generic hypergraph and an arbitrary injective outer map.

This completes the diary-leaf-pair application of (I3). The
manuscript's more general quantified hypothesis using the named
abstract `Env_G^i(S)` for arbitrary pairs in the generic
hypergraph is handled by the separate native common-source
representation and its remaining `Env` correspondence. Neither
cut-zero orientation nor flip/pre-diary completion follows here.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- Any two equal-full-2-type pairs of leaves of a complete
role-based diary have equal full target 2-types and lexicographic
orientations after the verified fused stabilisation embedding.

The protected source cut must include the diary markers 0,1,2.
The target cut is the exact predecessor-image cut
F(g(ψ i−1))+1 and the external map F need only be injective. -/
theorem orderedDiaryFusion_diaryLeafPairType_orientation
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F)
    {H : Ordered3Graph Nat}
    (D : DiaryLeafPriority.RoleDiary H)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (i a b c d : Nat) (hi : 3 ≤ i)
    (hia : i ≤ a) (hic : i ≤ c)
    (hab : a < b) (hcd : c < d)
    (ha : DiaryLeafPriority.IsLeaf H a)
    (hb : DiaryLeafPriority.IsLeaf H b)
    (hc : DiaryLeafPriority.IsLeaf H c)
    (hd : DiaryLeafPriority.IsLeaf H d)
    (hpair : H.SameTwoTypeBelow i a b c d) :
    let g := orderedDiaryFusion G K F hF
    let j := ψ i
    let N := F (g (j-1)) + 1
    K.SameTwoTypeBelow N
      (F (g (ψ a))) (F (g (ψ b)))
      (F (g (ψ c))) (F (g (ψ d))) ∧
    (DiaryLeafPriority.LexEarlier K
        (F (g (ψ a))) (F (g (ψ b))) ↔
      DiaryLeafPriority.LexEarlier K
        (F (g (ψ c))) (F (g (ψ d)))) := by
  by_cases hearly : H.oneMeetLevel a b < i
  · exact orderedDiaryFusion_twoTail_pairType_orientation
      G K F hF ψ hψ i a b c d (by omega)
      hia hic hab hcd hpair hearly
  · have hlate : i ≤ H.oneMeetLevel a b :=
      Nat.le_of_not_gt hearly
    exact orderedDiaryFusion_threeTail_leafPairType_orientation
      G K F hF D ψ hψ i a b c d hi
      hia hic hab hcd ha hb hc hd hpair hlate

end ATRFiniteDecoder
end ThreeUniformDiaries
